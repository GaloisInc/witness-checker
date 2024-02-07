use std::collections::{HashMap, HashSet};
use std::path::Path;
use clap::{App, Arg, ArgMatches};
use serde::{Serialize, Deserialize};
use cheesecloth::edit_trace::{self, Value, Format};
use cheesecloth::micro_ram::trace::InstrLookup;
use cheesecloth::micro_ram::types::{VersionedMultiExec, Trace, BbmdBlock, RamInstr, Opcode};
use cheesecloth::mode::if_mode::{Mode, with_mode};

fn parse_args() -> ArgMatches<'static> {
    App::new("bbmd_trace_hack")
        .about("rewrite non-bbmd trace to use bbmd")
        .arg(Arg::with_name("trace")
             .takes_value(true)
             .value_name("TRACE.CBOR")
             .help("MicroRAM execution trace")
             .required(true))
        .arg(Arg::with_name("output")
             .short("o")
             .long("output")
             .takes_value(true)
             .value_name("OUT.CBOR")
             .help("where to write the new trace using bbmd"))
        .get_matches()
}

struct Limits {
    mem: usize,
    advise: usize,
    mul_div: usize,
}

/// Try to decrement `x` by 1.  Returns `false` if `x` is already zero.
fn try_decrement(x: &mut usize) -> bool {
    if *x == 0 {
        false
    } else {
        *x -= 1;
        true
    }
}

impl Limits {
    /// Try to decrement the limits as appropriate for `opcode`.  Returns `false` if this failed
    /// because some limits are already zero.
    pub fn try_opcode(&mut self, opcode: Opcode) -> bool {
        match opcode {
            Opcode::And |
            Opcode::Or |
            Opcode::Xor |
            Opcode::Not |
            Opcode::Add |
            Opcode::Sub => true,
            Opcode::Mull |
            Opcode::Umulh |
            Opcode::Smulh |
            Opcode::Udiv |
            Opcode::Umod => try_decrement(&mut self.mul_div),
            Opcode::Shl |
            Opcode::Shr => true,

            Opcode::Cmpe |
            Opcode::Cmpa |
            Opcode::Cmpae |
            Opcode::Cmpg |
            Opcode::Cmpge => true,

            Opcode::Mov |
            Opcode::Cmov => true,

            Opcode::Jmp |
            Opcode::Cjmp |
            Opcode::Cnjmp => true,

            Opcode::Store1 |
            Opcode::Store2 |
            Opcode::Store4 |
            Opcode::Store8 |
            Opcode::Load1 |
            Opcode::Load2 |
            Opcode::Load4 |
            Opcode::Load8 |
            Opcode::Poison8 => try_decrement(&mut self.mem),

            Opcode::Read => panic!("Opcode::Read is unsupported"),
            Opcode::Answer => true,

            Opcode::Advise => try_decrement(&mut self.advise),

            Opcode::Sink1 |
            Opcode::Taint1 => true,

            Opcode::Stutter => true,
        }
    }
}

fn next_pc(instr: &RamInstr, pc: u64) -> Option<u64> {
    match instr.opcode() {
        Opcode::And |
        Opcode::Or |
        Opcode::Xor |
        Opcode::Not |
        Opcode::Add |
        Opcode::Sub |
        Opcode::Mull |
        Opcode::Umulh |
        Opcode::Smulh |
        Opcode::Udiv |
        Opcode::Umod |
        Opcode::Shl |
        Opcode::Shr => Some(pc + 1),

        Opcode::Cmpe |
        Opcode::Cmpa |
        Opcode::Cmpae |
        Opcode::Cmpg |
        Opcode::Cmpge => Some(pc + 1),

        Opcode::Mov |
        Opcode::Cmov => Some(pc + 1),

        Opcode::Jmp => {
            if instr.imm {
                Some(instr.op2)
            } else {
                // Indirect jump
                None
            }
        },
        Opcode::Cjmp |
        Opcode::Cnjmp => None,

        Opcode::Store1 |
        Opcode::Store2 |
        Opcode::Store4 |
        Opcode::Store8 |
        Opcode::Load1 |
        Opcode::Load2 |
        Opcode::Load4 |
        Opcode::Load8 |
        Opcode::Poison8 => Some(pc + 1),

        Opcode::Read => panic!("Opcode::Read is unsupported"),
        // To avoid an infinite loop in `mk_block`, we bail out after `Answer`.
        Opcode::Answer => None,

        Opcode::Advise => Some(pc + 1),

        Opcode::Sink1 |
        Opcode::Taint1 => Some(pc + 1),

        Opcode::Stutter => panic!("Opcode::Stutter is not supported"),
    }
}

fn mk_block(instrs: &InstrLookup, start_pc: u64) -> BbmdBlock {
    let mut pcs = vec![(start_pc, start_pc)];
    let mut cur_pc = start_pc;

    let mut limits = Limits {
        mem: 4,
        advise: 1,
        mul_div: 2,
    };

    loop {
        let instr = &instrs[cur_pc];
        if !limits.try_opcode(instr.opcode()) {
            break;
        }

        match pcs.last_mut() {
            Some(&mut (_, ref mut x)) if *x == cur_pc => {
                *x += 1;
            },
            _ => {
                pcs.push((cur_pc, cur_pc + 1));
            },
        }

        // Try to update the current PC.
        let next_pc = match next_pc(instr, cur_pc) {
            Some(x) => x,
            None => break,
        };
        cur_pc = next_pc;

        // For examples that just end without a terminating `answer`, don't go past the end of the
        // program.
        if instrs.get(cur_pc).is_none() {
            break;
        }
    }

    BbmdBlock { pcs }
}

fn rounded_step_count(n: usize) -> usize {
    // Round values >= 1000 to two sig figs; round smaller values to one sig fig.  Single-digit
    // values are always rounded up to 10.
    let target = if n < 10 {
        return 10;
    } else if n < 1000 {
        10
    } else {
        100
    };
    let mut n = n;
    let mut mul = 1;
    while n >= target {
        n = (n + 9) / 10;
        mul *= 10;
    }
    n * mul
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TraceState {
    pc: u64,
    regs: Vec<u64>,
}

type FlatTrace = Vec<TraceState>;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TraceChunk {
    segment: usize,
    states: Vec<TraceState>,
}

type ChunkedTrace = Vec<TraceChunk>;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct BbmdTraceChunk {
    block: usize,
    states: Vec<TraceState>,
}

type BbmdChunkedTrace = Vec<BbmdTraceChunk>;

fn run(args: &ArgMatches) -> Result<(), String> {
    let in_path = Path::new(args.value_of_os("trace")
        .ok_or("cbor path is required")?);
    match Format::from_path(in_path) {
        Format::Yaml => run_typed::<serde_yaml::Value>(args, in_path),
        Format::Cbor => run_typed::<serde_cbor::Value>(args, in_path),
        Format::Json => todo!("json support"),
    }
}

fn run_typed<V: Value>(args: &ArgMatches, in_path: &Path) -> Result<(), String> {
    let mut v = edit_trace::parse_file::<V>(in_path)?;
    let (exec, v_exec) = edit_trace::get_exec_mut(&mut v)?;

    let it = match exec.trace {
        Trace::Instr(ref x) => x,
        Trace::Bbmd(_) => return Err("trace is already in bbmd format".into()),
    };

    let instrs = InstrLookup::new(&exec.program);

    // Build a block starting from each valid PC.
    let mut blocks = Vec::new();
    let mut pc_block_idxs = HashMap::new();
    for pc in instrs.iter_pcs() {
        let idx = blocks.len();
        let block = mk_block(&instrs, pc);
        blocks.push(block);
        debug_assert!(!pc_block_idxs.contains_key(&pc), "duplicate entry for pc = {}", pc);
        pc_block_idxs.insert(pc, idx);
    }

    // Build `bbmd_blocks` list.
    v_exec.remove_key("segments");
    v_exec.insert_key("bbmd_blocks", V::from_serialize(&blocks)?);
    eprintln!("bbmd_blocks: {} entries", blocks.len());

    // Build new `trace` list.
    // TODO: remove stutter
    let v_trace = v_exec.get_key("trace").unwrap();
    let states = if let Ok(flat) = v_trace.parse::<FlatTrace>() {
        flat.into_iter().skip(1).collect::<Vec<_>>()
    } else if let Ok(chunked) = v_trace.parse::<ChunkedTrace>() {
        chunked.into_iter().flat_map(|c| c.states.into_iter()).collect::<Vec<_>>()
    } else {
        panic!("failed to parse trace")
    };

    let mut trace = Vec::new();
    let mut i = 0;
    let mut cur_pc = 0;
    let mut blocks_used = HashSet::new();
    while i < states.len() {
        let block_idx = pc_block_idxs[&cur_pc];
        let block = &blocks[block_idx];
        let n = block.pcs.iter().map(|&(lo, hi)| hi - lo).sum();
        let mut chunk = BbmdTraceChunk {
            block: block_idx,
            states: Vec::with_capacity(n as usize),
        };
        for _ in 0..n {
            let state = states.get(i).cloned().unwrap_or_else(|| states.last().unwrap().clone());
            cur_pc = state.pc;
            chunk.states.push(state);
            i += 1;
        }
        trace.push(chunk);
        blocks_used.insert(block_idx);
    }
    v_exec.insert_key("trace", V::from_serialize(&trace)?);
    eprintln!("trace: {} entries", trace.len());
    eprintln!("used {} / {} blocks", blocks_used.len(), blocks.len());

    // Set `params.trace_len` based on actual trace length.
    let step_count = rounded_step_count(trace.len());
    edit_trace::set_param(v_exec, "trace_len", V::from_serialize(&step_count)?);
    eprintln!("set trace_len = {}", step_count);

    // Add `bbmd` feature.
    v.get_index_mut(1).unwrap().push_array(V::new_string("bbmd".into()));

    if let Some(out_path) = args.value_of_os("output") {
        edit_trace::write_output(Path::new(out_path), &v)?;
    }

    Ok(())
}


fn main() -> Result<(), String> {
    let mode = Mode::MemorySafety;
    unsafe {
        with_mode(mode, || {
            let args = parse_args();
            run(&args)
        })
    }
}
