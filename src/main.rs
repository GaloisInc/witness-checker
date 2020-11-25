use std::collections::{HashMap, HashSet};
use std::fs;
use std::io;
use std::iter;
use std::mem::{self, MaybeUninit};
use std::path::Path;
use std::ptr;
use bumpalo::Bump;
use clap::{App, Arg, ArgMatches};
use num_traits::One;

use cheesecloth::wire_assert;
use cheesecloth::debug;
use cheesecloth::eval::{self, Evaluator, CachingEvaluator};
use cheesecloth::ir::circuit::{Circuit, Wire, GateKind, GadgetKindRef};
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::gadget::arith::BuilderExt as _;
use cheesecloth::lower::{self, run_pass, run_pass_debug};
use cheesecloth::micro_ram::context::Context;
use cheesecloth::micro_ram::fetch::Fetch;
use cheesecloth::micro_ram::mem::Memory;
use cheesecloth::micro_ram::parse::ParseExecution;
use cheesecloth::micro_ram::types::{
    RamInstr, RamState, RamStateRepr, MemPort, MemOpKind, Opcode, Advice, REG_NONE, REG_PC,
    MEM_PORT_UNUSED_CYCLE,
};


fn parse_args() -> ArgMatches<'static> {
    App::new("witness-checker")
        .about("generate a witness checker circuit for a given MicroRAM execution trace")
        .arg(Arg::with_name("trace")
             .takes_value(true)
             .value_name("TRACE.CBOR")
             .help("MicroRAM execution trace")
             .required(true))
        .arg(Arg::with_name("zkif-out")
             .long("zkif-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output zkinterface circuit representation in this directory"))
        .arg(Arg::with_name("validate-only")
             .long("validate-only")
             .help("check only that the trace is valid; don't require it to demonstrate a bug"))
        .arg(Arg::with_name("expect-zero")
             .long("expect-zero")
             .help("check that r0 == 0 in the final state"))
        .arg(Arg::with_name("stats")
             .long("stats")
             .help("print info about the size of the circuit"))
        .arg(Arg::with_name("check-steps")
             .long("check-steps")
             .takes_value(true)
             .value_name("1")
             .help("check state against the trace every D steps"))
        .after_help("With no output options, prints the result of evaluating the circuit.")
        .get_matches()
}



fn operand_value<'a>(
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
    op: TWire<'a, u64>,
    imm: TWire<'a, bool>,
) -> TWire<'a, u64> {
    let reg_val = b.index(&s.regs, op, |b, i| b.lit(i as u64));
    b.mux(imm, op, reg_val)
}

pub struct CalcIntermediate<'a> {
    pub x: TWire<'a,u64>,
    pub y: TWire<'a,u64>,
    pub result: TWire<'a,u64>,
}


fn calc_step<'a>(
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    advice: TWire<'a, u64>,
    s1: &TWire<'a, RamState>,
) -> (TWire<'a, RamState>,CalcIntermediate<'a>) {
    let _g = b.scoped_label(format_args!("calc_step/cycle {}", cycle));

    // TODO: Where do we get instr from? PC wire of s1? Or still advice?
    
    let mut cases = Vec::new();
    let mut add_case = |op, result, dest| {
        let op_match = b.eq(b.lit(op as u8), instr.opcode);
        let parts = TWire::<(_, _)>::new((result, dest));
        cases.push(TWire::<(_, _)>::new((op_match, parts)));
    };

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u8));
    let y = operand_value(b, s1, instr.op2, instr.imm);

    {
        let result = b.and(x, y);
        add_case(Opcode::And, result, instr.dest);
    }

    {
        let result = b.or(x, y);
        add_case(Opcode::Or, result, instr.dest);
    }

    {
        let result = b.xor(x, y);
        add_case(Opcode::Xor, result, instr.dest);
    }

    {
        let result = b.not(y);
        add_case(Opcode::Not, result, instr.dest);
    }

    {
        add_case(Opcode::Add, b.add(x, y), instr.dest);
    }

    {
        add_case(Opcode::Sub, b.sub(x, y), instr.dest);
    }

    {
        add_case(Opcode::Mull, b.mul(x, y), instr.dest);
    }

    {
        let (_, high) = *b.wide_mul(x, y);
        add_case(Opcode::Umulh, high, instr.dest);
    }

    {
        let (_, high_s) = *b.wide_mul(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        // TODO: not sure this gives the right overflow value - what if high = -1?
        add_case(Opcode::Smulh, b.cast::<_, u64>(high_s), instr.dest);
    }

    {
        let result = b.div(x, y);
        add_case(Opcode::Udiv, result, instr.dest);
    }

    {
        let result = b.mod_(x, y);
        add_case(Opcode::Umod, result, instr.dest);
    }

    {
        let result = b.shl(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shl, result, instr.dest);
    }

    {
        let result = b.shr(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shr, result, instr.dest);
    }


    {
        let result = b.cast::<_, u64>(b.eq(x, y));
        add_case(Opcode::Cmpe, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.gt(x, y));
        add_case(Opcode::Cmpa, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.ge(x, y));
        add_case(Opcode::Cmpae, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.gt(b.cast::<_, i64>(x), b.cast::<_, i64>(y)));
        add_case(Opcode::Cmpg, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.ge(b.cast::<_, i64>(x), b.cast::<_, i64>(y)));
        add_case(Opcode::Cmpge, result, instr.dest);
    }


    {
        add_case(Opcode::Mov, y, instr.dest);
    }

    {
        let dest = b.mux(b.neq_zero(x), instr.dest, b.lit(REG_NONE));
        add_case(Opcode::Cmov, y, dest);
    }


    {
        add_case(Opcode::Jmp, y, b.lit(REG_PC));
    }

    // TODO: Double check. Is this `x`?
    // https://gitlab-ext.galois.com/fromager/cheesecloth/MicroRAM/-/merge_requests/33/diffs#d54c6573feb6cf3e6c98b0191e834c760b02d5c2_94_71
    {
        let dest = b.mux(b.neq_zero(x), b.lit(REG_PC), b.lit(REG_NONE));
        add_case(Opcode::Cjmp, y, dest);
    }

    {
        let dest = b.mux(b.neq_zero(x), b.lit(REG_NONE), b.lit(REG_PC));
        add_case(Opcode::Cnjmp, y, dest);
    }

    {
        let result = mem_port.value;
        add_case(Opcode::Load, result, instr.dest);
    }

    {
        add_case(Opcode::Store, b.lit(0), b.lit(REG_NONE));
    }

    {
        add_case(Opcode::Poison, b.lit(0), b.lit(REG_NONE));
    }

    {
        // TODO: dummy implementation of `Answer` as a no-op infinite loop
        add_case(Opcode::Answer, s1.pc, b.lit(REG_PC));
    }

    {
        add_case(Opcode::Advise, advice, instr.dest);
    }

    {
        // A no-op that doesn't advance the `pc`.  Specifically, this works by jumping to the
        // current `pc`.
        add_case(Opcode::Stutter, s1.pc, b.lit(REG_PC));
    }

    let (result, dest) = *b.mux_multi(&cases, b.lit((0, REG_NONE)));

    let mut regs = Vec::with_capacity(s1.regs.len());
    for (i, &v_old) in s1.regs.iter().enumerate() {
        let is_dest = b.eq(b.lit(i as u8), dest);
        regs.push(b.mux(is_dest, result, v_old));
    }

    let pc_is_dest = b.eq(b.lit(REG_PC), dest);
    let pc = b.mux(pc_is_dest, result, b.add(s1.pc, b.lit(1)));

    let s2 = RamStateRepr { pc, regs };
    let im = CalcIntermediate { x, y, result };
    (TWire::new(s2),im)
}

fn check_state<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    calc_s: &TWire<'a, RamState>,
    trace_s: &TWire<'a, RamState>,
) {
    let _g = b.scoped_label(format_args!("check_state/cycle {}", cycle));

    for (i, (&v_calc, &v_new)) in calc_s.regs.iter().zip(trace_s.regs.iter()).enumerate() {
        wire_assert!(
            cx, b.eq(v_new, v_calc),
            "cycle {} sets reg {} to {} (expected {})",
            cycle, i, cx.eval(v_new), cx.eval(v_calc),
        );
    }

    wire_assert!(
        cx, b.eq(trace_s.pc, calc_s.pc),
        "cycle {} sets pc to {} (expected {})",
        cycle, cx.eval(trace_s.pc), cx.eval(calc_s.pc),
    );
}

fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    calc_im: &CalcIntermediate<'a>,
) {
    let _g = b.scoped_label(format_args!("check_step/cycle {}", cycle));

    let x = calc_im.x;
    let y = calc_im.y;
    let result = calc_im.result;

    // If the instruction is a store, load, or poison, we need additional checks to make sure the
    // fields of `mem_port` match the instruction operands.
    let is_load = b.eq(instr.opcode, b.lit(Opcode::Load as u8));
    let is_store = b.eq(instr.opcode, b.lit(Opcode::Store as u8));
    let is_poison = b.eq(instr.opcode, b.lit(Opcode::Poison as u8));
    let is_store_like = b.or(is_store, is_poison);
    let is_mem = b.or(is_load, is_store_like);

    let expect_value = b.mux(is_store_like, x, result);
    cx.when(b, is_mem, |cx| {
        wire_assert!(
            cx, b.eq(mem_port.addr, y),
            "cycle {}'s mem port has address {} (expected {})",
            cycle, cx.eval(mem_port.addr), cx.eval(y),
        );
        let flag_ops = [
            (is_load, MemOpKind::Read),
            (is_store, MemOpKind::Write),
            (is_poison, MemOpKind::Poison),
        ];
        for &(flag, op) in flag_ops.iter() {
            cx.when(b, flag, |cx| {
                wire_assert!(
                    cx, b.eq(mem_port.op, b.lit(op)),
                    "cycle {}'s mem port has op kind {} (expected {}, {:?})",
                    cycle, cx.eval(mem_port.op.repr), op as u8, op,
                );
            });
        }
        wire_assert!(
            cx, b.eq(mem_port.value, expect_value),
            "cycle {}'s mem port (op {}) has value {} (expected {})",
            cycle, cx.eval(mem_port.op.repr), cx.eval(mem_port.value), cx.eval(expect_value),
        );
    });

    // Either `mem_port.cycle == cycle` and this step is a mem op, or `mem_port.cycle ==
    // MEM_PORT_UNUSED_CYCLE` and this is not a mem op.  Other `mem_port.cycle` values are invalid.
    let expect_cycle = b.mux(is_mem, b.lit(cycle), b.lit(MEM_PORT_UNUSED_CYCLE));
    wire_assert!(
        cx, b.eq(mem_port.cycle, expect_cycle),
        "cycle {} mem port cycle number is {} (expected {}; mem op? {})",
        cycle, cx.eval(mem_port.cycle), cx.eval(expect_cycle), cx.eval(is_mem),
    );
}

fn check_first<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
) {
    let _g = b.scoped_label("check_first");
    wire_assert!(
        cx, b.eq(s.pc, b.lit(0)),
        "initial pc is {} (expected {})",
        cx.eval(s.pc), 0,
    );
    for (i, &r) in s.regs.iter().enumerate().skip(1) {
        wire_assert!(
            cx, b.eq(r, b.lit(0)),
            "initial r{} has value {} (expected {})",
            i, cx.eval(r), 0,
        );
    }
}

fn check_last<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
    expect_zero: bool,
) {
    let _g = b.scoped_label("check_last");
    if expect_zero {
        wire_assert!(
            cx, b.eq(s.regs[0], b.lit(0)),
            "final r0 is {} (expected {})",
            cx.eval(s.regs[0]), 0,
        );
    }
}

struct PassRunner<'a> {
    // Wrap everything in `MaybeUninit` to prevent the compiler from realizing that we have
    // overlapping `&` and `&mut` references.
    cur: MaybeUninit<&'a mut Bump>,
    next: MaybeUninit<&'a mut Bump>,
    /// Invariant: the underlying `Gate` of every wire in `wires` is allocated from the `cur`
    /// arena.
    wires: MaybeUninit<Vec<Wire<'a>>>,
}

const DEBUG_PASSES: bool = false;

impl<'a> PassRunner<'a> {
    pub fn new(a: &'a mut Bump, b: &'a mut Bump, wires: Vec<Wire>) -> PassRunner<'a> {
        a.reset();
        b.reset();
        let cur = MaybeUninit::new(a);
        let next = MaybeUninit::new(b);
        let wires = unsafe {
            // Transfer all wires into the `cur` arena.
            let arena: &Bump = &**cur.as_ptr();
            let c = Circuit::new(arena);
            let wires = run_pass(&c, wires, |c, _old, gk| c.gate(gk));
            MaybeUninit::new(wires)
        };

        PassRunner { cur, next, wires }
    }

    // FIXME: using `'a` instead of a fresh lifetime (`for <'b>`) potentially allows the closure to
    // stash a `GateKind` or `Wire` somewhere and use it after the arena has been `reset`.
    // However, this also makes it hard to apply stateful transformation passes (`const_fold`).
    pub fn run(&mut self, f: impl FnMut(&Circuit<'a>, Wire, GateKind<'a>) -> Wire<'a>) {
        unsafe {
            {
                let arena: &Bump = &**self.next.as_ptr();
                let c = Circuit::new(arena);
                let wires = mem::replace(&mut *self.wires.as_mut_ptr(), Vec::new());
                let wires = if DEBUG_PASSES {
                    run_pass_debug(&c, wires, f)
                } else {
                    run_pass(&c, wires, f)
                };
                *self.wires.as_mut_ptr() = wires;
            }
            // All `wires` are now allocated from `self.next`, leaving `self.cur` unused.
            (*self.cur.as_mut_ptr()).reset();
            ptr::swap(self.cur.as_mut_ptr(), self.next.as_mut_ptr());
        }
    }

    pub fn finish(self) -> (Circuit<'a>, Vec<Wire<'a>>) {
        unsafe {
            let arena: &Bump = &**self.cur.as_ptr();
            let c = Circuit::new(arena);
            let wires = ptr::read(self.wires.as_ptr());
            (c, wires)
        }
    }
}

fn main() -> io::Result<()> {
    let args = parse_args();

    #[cfg(not(feature = "bellman"))]
    if args.is_present("zkif-out") {
        eprintln!("error: zkinterface output is not supported - build with `--features bellman`");
        std::process::exit(1);
    }


    let arena = Bump::new();
    let c = Circuit::new(&arena);
    let b = Builder::new(&c);
    let cx = Context::new(&c);

    // Load the program and trace from files
    let trace_path = Path::new(args.value_of_os("trace").unwrap());
    let content = fs::read(trace_path).unwrap();
    let parse_exec: ParseExecution = match trace_path.extension().and_then(|os| os.to_str()) {
        Some("yaml") => serde_yaml::from_slice(&content).unwrap(),
        Some("cbor") => serde_cbor::from_slice(&content).unwrap(),
        Some("json") => serde_json::from_slice(&content).unwrap(),
        _ => serde_cbor::from_slice(&content).unwrap(),
    };
    let exec = parse_exec.into_inner();

    let mut trace = Vec::new();
    for (i, state) in exec.trace.iter().enumerate() {
        let _g = b.scoped_label(format_args!("state {}", i));
        trace.push(RamState::secret_with_value(&b, state.clone()));
    }

    // Set up memory ports and check consistency.
    let mut mem = Memory::new(false);
    for seg in &exec.init_mem {
        mem.init_segment(&b, seg);
    }
    let cycle_mem_ports = mem.add_cycles(
        &cx, &b,
        exec.params.trace_len - 1,
        exec.params.sparsity.mem_op,
        |i| {
            let advs = exec.advice.get(&(i as u64 + 1)).map_or(&[] as &[_], |x| x);
            (advs, i as u32)
        },
    );
    mem.assert_consistent(&cx, &b);

    // Gather `Advise` and `Stutter` advice values
    let mut advices = HashMap::new();
    let mut stutters = HashSet::new();
    for (&i, advs) in &exec.advice {
        for adv in advs {
            match *adv {
                Advice::Advise { advise } => {
                    advices.insert(i as u32 - 1, advise);
                },
                Advice::Stutter => {
                    stutters.insert(i as u32 - 1);
                },
                _ => {},
            }
        }
    }

    // Set up instruction-fetch ports and check consistency.
    let mut fetch = Fetch::new(false);
    fetch.init_program(&b, &exec.program);
    let cycle_fetch_ports = fetch.add_cycles(
        &b,
        exec.params.trace_len - 1,
        &exec.program,
        |i| exec.trace[i].pc,
    );
    fetch.assert_consistent(&cx, &b);

    // Generate IR code to check the trace

    check_first(&cx, &b, trace.first().unwrap());

    let check_steps = args.value_of("check-steps").and_then(|c| c.parse().ok()).map(|c| if c <= 0 {1} else {c}).unwrap_or(1);
    let mut prev_s = trace[0].clone();
    let mut max_i = 0;
    for (i, s2) in trace.iter().skip(1).enumerate() {
        max_i = i;

        // Fetch the instruction to execute.  If the `Stutter` advice is present, the instruction
        // opcode is actually replaced by `Opcode::Stutter`.
        let mut instr = cycle_fetch_ports.get_instr(i);
        let stutter = b.secret(Some(stutters.contains(&(i as u32))));
        instr.opcode = b.mux(stutter, b.lit(Opcode::Stutter as u8), instr.opcode);
        let instr = instr;

        let port = cycle_mem_ports.get(&b, i);
        let advice = b.secret(Some(*advices.get(&(i as u32)).unwrap_or(&0)));

        let (calc_s, calc_im) = calc_step(&b, i as u32, instr, &port, advice, &prev_s);

        // Check trace every D steps. 
        if i % check_steps == 0 {
            check_state(&cx, &b, i as u32, &calc_s, s2);
            prev_s = s2.clone();
        } else {
            prev_s = calc_s.clone();
        }
        check_step(&cx, &b, i as u32, instr, &port, &calc_im);
    }
    // We rely on the loop running once for every `i` in `0 .. num_steps`.
    assert_eq!(max_i + 1, exec.params.trace_len as usize - 1);

    check_last(&cx, &b, trace.last().unwrap(), args.is_present("expect-zero"));

    // Check that the fetch ports are consistent with the steps taken.
    for (i, port) in cycle_fetch_ports.iter().enumerate() {
        wire_assert!(
            &cx,
            b.eq(port.addr, trace[i].pc),
            "fetch on cycle {} accesses address {:x} (expected {:x})",
            i, cx.eval(port.addr), cx.eval(trace[i].pc),
        );
    }

    // Collect assertions and bugs.
    drop(b);
    let (asserts, bugs) = cx.finish();
    let asserts = asserts.into_iter().map(|tw| tw.repr).collect::<Vec<_>>();
    let bugs = bugs.into_iter().map(|tw| tw.repr).collect::<Vec<_>>();

    // The statement is accepted if all assertions hold.
    let accepted = if args.is_present("validate-only") {
        c.all_true(asserts.iter().cloned())
    } else {
        c.and(
            c.all_true(asserts.iter().cloned()),
            c.any_true(bugs.iter().cloned()),
        )
    };

    // Concatenate accepted, asserts, bugs.
    let num_asserts = asserts.len();
    let flags =
        iter::once(accepted)
            .chain(asserts.into_iter())
            .chain(bugs.into_iter())
            .collect::<Vec<_>>();

    if args.is_present("stats") {
        eprintln!(" ===== stats: before lowering =====");
        debug::count_gates::count_gates(&flags);
        eprintln!(" ===== end stats (before lowering) =====");
    }

    let mut arena1 = Bump::new();
    let mut arena2 = Bump::new();
    let mut passes = PassRunner::new(&mut arena1, &mut arena2, flags);

    let gadget_supported = |g: GadgetKindRef| {
        use cheesecloth::gadget::bit_pack::{ConcatBits, ExtractBits};
        let mut ok = false;
        if args.is_present("zkif-out") {
            ok = ok || g.cast::<ConcatBits>().is_some();
            ok = ok || g.cast::<ExtractBits>().is_some();
        }
        if args.is_present("scale-out") {
        }
        ok
    };

    passes.run(lower::bit_pack::concat_bits_flat);
    // TODO: need a better way to handle passes that must be run to fixpoint
    passes.run(lower::gadget::decompose_gadgets(|g| !gadget_supported(g)));
    passes.run(lower::gadget::decompose_gadgets(|g| !gadget_supported(g)));
    passes.run(lower::bundle::unbundle_mux);
    passes.run(lower::bundle::simplify);
    passes.run(lower::const_fold::const_fold(&c));
    passes.run(lower::int::mod_to_div);
    passes.run(lower::int::non_constant_shift);
    #[cfg(feature = "bellman")]
    if args.is_present("zkif-out") {
        passes.run(lower::int::compare_to_greater_or_equal_to_zero);
    }
    passes.run(lower::bool_::mux);
    passes.run(lower::bool_::compare_to_logic);
    passes.run(lower::bool_::not_to_xor);
    let (c, flags) = passes.finish();

    if args.is_present("stats") {
        eprintln!(" ===== stats: after lowering =====");
        debug::count_gates::count_gates(&flags);
        eprintln!(" ===== end stats (after lowering) =====");
    }

    {
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);
        let flag_vals = flags.iter().map(|&w| {
            ev.eval_wire(w).as_ref().and_then(|v| v.as_single()).unwrap().is_one()
        }).collect::<Vec<_>>();

        let asserts_ok: u32 = flag_vals[1 .. 1 + num_asserts].iter().map(|&ok| ok as u32).sum();
        let bugs_ok: u32 = flag_vals[1 + num_asserts ..].iter().map(|&ok| ok as u32).sum();

        eprintln!(
            "internal evaluator: {} asserts passed, {} failed; found {} bugs; overall status: {}",
            asserts_ok, num_asserts as u32 - asserts_ok, bugs_ok,
            if flag_vals[0] { "GOOD" } else { "BAD" },
        );
    }

    #[cfg(feature = "bellman")]
    if let Some(dest) = args.value_of_os("zkif-out") {
        use cheesecloth::back::zkif::backend::{Backend, Scalar};
        use std::fs::remove_file;
        use zkinterface::{cli::{cli, Options}, clean_workspace};

        let accepted = flags[0];

        // Clean workspace.
        let workspace = Path::new(dest);
        clean_workspace(workspace).unwrap();

        // Generate the circuit and witness.
        let mut backend = Backend::new(workspace, true);

        backend.enforce_true(accepted);

        // Write files.
        backend.finish().unwrap();

        eprintln!("validating zkif...");

        // Validate the circuit and witness.
        cli(&Options {
            tool: "simulate".to_string(),
            paths: vec![workspace.to_path_buf()],
        }).unwrap();

        // Print statistics.
        cli(&Options {
            tool: "stats".to_string(),
            paths: vec![workspace.to_path_buf()],
        }).unwrap();
    }

    // Unused in some configurations.
    let _ = num_asserts;

    Ok(())
}
