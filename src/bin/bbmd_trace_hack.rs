use std::collections::HashSet;
use std::collections::hash_map::{HashMap, Entry};
use std::path::Path;
use clap::{App, Arg, ArgMatches};
use serde::{Serialize, Deserialize};
use cheesecloth::edit_trace::{self, Value, Format};
use cheesecloth::micro_ram::trace::InstrLookup;
use cheesecloth::micro_ram::types::{
    VersionedMultiExec, Trace, BbmdBlock, RamInstr, Opcode, Advice,
};
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
        .arg(Arg::with_name("all-blocks")
             .long("all-blocks")
             .help("generate blocks for all PCs, not just ones that are used"))
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
        mem: 2,
        advise: 1,
        mul_div: 1,
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

#[derive(Clone, Debug, Default)]
struct PcBlocks {
    blocks: Vec<BbmdBlock>,
    pc_block_idxs: HashMap<u64, usize>,
}

impl PcBlocks {
    pub fn get(&mut self, instrs: &InstrLookup, pc: u64) -> (usize, &BbmdBlock) {
        let idx = match self.pc_block_idxs.entry(pc) {
            Entry::Vacant(e) => {
                let idx = self.blocks.len();
                self.blocks.push(mk_block(instrs, pc));
                e.insert(idx);
                idx
            },
            Entry::Occupied(e) => {
                *e.get()
            },
        };
        (idx, &self.blocks[idx])
    }
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
    let mut pc_blocks = PcBlocks::default();

    // Pregenerate blocks for all possible starting PCs.
    if args.is_present("all-blocks") {
        for pc in instrs.iter_pcs() {
            let _ = pc_blocks.get(&instrs, pc);
        }
    }

    // Process the advice map to remove Stutter advice.
    let v_advice = v_exec.get_key_mut("advice").unwrap();
    let mut v_advice_new = V::new_map();
    let mut num_removed = 0;
    let v_str_stutter = V::new_string("Stutter".into());
    for k in v_advice.keys() {
        let v_advs = v_advice.get_key_any(&k).unwrap();
        if let Some(v_adv0) = v_advs.get_index(0) {
            if v_adv0.get_index(0).unwrap() == &v_str_stutter {
                num_removed += 1;
                // Don't insert into `v_advice_new`.
                continue;
            }
        }

        let old_i = k.parse::<u64>().unwrap();
        let new_i = old_i - num_removed;
        v_advice_new.insert_key_any(V::new_u64(new_i), v_advs.clone());
    }
    *v_advice = v_advice_new;

    // Build a list of indices of states to be discarded.  We don't do this while cleaning up the
    // advice map because the indices in that map may be off by one depending on whether or not
    // `Feature::PreAdvice` is set.
    let mut stutter_indices = HashSet::new();
    for (&idx, advs) in exec.advice.iter() {
        if advs.iter().any(|adv| matches!(*adv, Advice::Stutter)) {
            // `idx` is the index of the stutter's post state, which is the state we want to
            // delete from the trace.
            stutter_indices.insert(idx as usize);
        }
    }

    // Build new `trace` list.
    let v_trace = v_exec.get_key("trace").unwrap();
    let states = if let Ok(flat) = v_trace.parse::<FlatTrace>() {
        flat.into_iter().skip(1).collect::<Vec<_>>()
    } else if let Ok(chunked) = v_trace.parse::<ChunkedTrace>() {
        chunked.into_iter().flat_map(|c| c.states.into_iter()).collect::<Vec<_>>()
    } else {
        panic!("failed to parse trace")
    };
    // Remove duplicate states introduced by stutter advice.  Note that state 0 is omitted from
    // `states`, so the `enumerate` indices are off by 1.
    let states = states.into_iter().enumerate()
        .filter(|(i, _)| !stutter_indices.contains(&(i + 1)))
        .map(|(_, x)| x)
        .collect::<Vec<_>>();

    let mut trace = Vec::new();
    let mut i = 0;
    let mut cur_pc = 0;
    let mut blocks_used = HashSet::new();
    while i < states.len() {
        let (block_idx, block) = pc_blocks.get(&instrs, cur_pc);
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
    eprintln!("used {} / {} blocks", blocks_used.len(), pc_blocks.blocks.len());

    // Set `bbmd_blocks` list.  This is deferred until after the trace is built in case more blocks
    // are added to `pc_blocks` during trace generation.
    v_exec.remove_key("segments");
    v_exec.insert_key("bbmd_blocks", V::from_serialize(&pc_blocks.blocks)?);

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
