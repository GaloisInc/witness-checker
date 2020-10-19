use std::collections::HashMap;
use std::fs;
use std::io;
use std::iter;
use std::mem::{self, MaybeUninit};
use std::path::Path;
use std::ptr;
use bumpalo::Bump;
use clap::{App, Arg, ArgMatches};
use log::*;
use num_traits::One;

use cheesecloth::{wire_assert, wire_bug_if};
use cheesecloth::debug;
use cheesecloth::eval::{self, Evaluator, CachingEvaluator};
use cheesecloth::ir::circuit::{Circuit, Wire, GateKind, GadgetKindRef};
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::gadget::arith::BuilderExt as _;
use cheesecloth::lower::{self, run_pass};
use cheesecloth::sort;
use cheesecloth::micro_ram::context::Context;
use cheesecloth::micro_ram::types::{
    Execution, RamInstr, RamState, RamStateRepr, MemPort, MemOpKind, PackedMemPort, FetchPort,
    PackedFetchPort, Opcode, Advice, REG_NONE, REG_PC, MEM_PORT_UNUSED_CYCLE,
    MEM_PORT_PRELOAD_CYCLE,
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
    pub mem_port: TWire<'a,MemPort>,
}


fn calc_step<'a>(
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_ports: &[TWire<'a, MemPort>],
    advice: TWire<'a, u64>,
    s1: &TWire<'a, RamState>,
) -> (TWire<'a, RamState>,CalcIntermediate<'a>) {
    let _g = b.scoped_label(format_args!("calc_step/cycle {}", cycle));

    // TODO: Where do we get instr from? PC wire of s1? Or still advice?
    
    let mut cases = Vec::new();
    let mut add_case = |op, result, dest, flag| {
        let op_match = b.eq(b.lit(op as u8), instr.opcode);
        let parts = TWire::<(_, _, _)>::new((result, dest, flag));
        cases.push(TWire::<(_, _)>::new((op_match, parts)));
    };

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u8));
    let y = operand_value(b, s1, instr.op2, instr.imm);

    let mem_port = b.select(
        mem_ports,
        b.lit(MemPort::default()),
        |port| b.eq(port.cycle, b.lit(cycle)),
    );

    {
        let result = b.and(x, y);
        add_case(Opcode::And, result, instr.dest, s1.flag);
    }

    {
        let result = b.or(x, y);
        add_case(Opcode::Or, result, instr.dest, s1.flag);
    }

    {
        let result = b.xor(x, y);
        add_case(Opcode::Xor, result, instr.dest, s1.flag);
    }

    {
        let result = b.not(y);
        add_case(Opcode::Not, result, instr.dest, s1.flag);
    }

    {
        add_case(Opcode::Add, b.add(x, y), instr.dest, s1.flag);
    }

    {
        add_case(Opcode::Sub, b.sub(x, y), instr.dest, s1.flag);
    }

    {
        add_case(Opcode::Mull, b.mul(x, y), instr.dest, s1.flag);
    }

    {
        let (_, high) = *b.wide_mul(x, y);
        add_case(Opcode::Umulh, high, instr.dest, s1.flag);
    }

    {
        let (_, high_s) = *b.wide_mul(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        // TODO: not sure this gives the right overflow value - what if high = -1?
        add_case(Opcode::Smulh, b.cast::<_, u64>(high_s), instr.dest, s1.flag);
    }

    {
        let result = b.div(x, y);
        add_case(Opcode::Udiv, result, instr.dest, s1.flag);
    }

    {
        let result = b.mod_(x, y);
        add_case(Opcode::Umod, result, instr.dest, s1.flag);
    }

    {
        let result = b.shl(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shl, result, instr.dest, s1.flag);
    }

    {
        let result = b.shr(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shr, result, instr.dest, s1.flag);
    }


    {
        let flag = b.eq(x, y);
        add_case(Opcode::Cmpe, b.lit(0), b.lit(REG_NONE), flag);
    }

    {
        let flag = b.gt(x, y);
        add_case(Opcode::Cmpa, b.lit(0), b.lit(REG_NONE), flag);
    }

    {
        let flag = b.ge(x, y);
        add_case(Opcode::Cmpae, b.lit(0), b.lit(REG_NONE), flag);
    }

    {
        let flag = b.gt(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        add_case(Opcode::Cmpg, b.lit(0), b.lit(REG_NONE), flag);
    }

    {
        let flag = b.gt(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        add_case(Opcode::Cmpge, b.lit(0), b.lit(REG_NONE), flag);
    }


    {
        add_case(Opcode::Mov, y, instr.dest, s1.flag);
    }

    {
        let dest = b.mux(s1.flag, instr.dest, b.lit(REG_NONE));
        add_case(Opcode::Cmov, y, dest, s1.flag);
    }


    {
        add_case(Opcode::Jmp, y, b.lit(REG_PC), s1.flag);
    }

    {
        let dest = b.mux(s1.flag, b.lit(REG_PC), b.lit(REG_NONE));
        add_case(Opcode::Cjmp, y, dest, s1.flag);
    }

    {
        let dest = b.mux(s1.flag, b.lit(REG_NONE), b.lit(REG_PC));
        add_case(Opcode::Cnjmp, y, dest, s1.flag);
    }

    {
        let result = mem_port.value;
        add_case(Opcode::Load, result, instr.dest, s1.flag);
    }

    {
        add_case(Opcode::Store, b.lit(0), b.lit(REG_NONE), s1.flag);
    }

    {
        add_case(Opcode::Poison, b.lit(0), b.lit(REG_NONE), s1.flag);
    }

    {
        // TODO: dummy implementation of `Answer` as a no-op infinite loop
        add_case(Opcode::Answer, s1.pc, b.lit(REG_PC), s1.flag);
    }

    {
        add_case(Opcode::Advise, advice, instr.dest, s1.flag);
    }

    let (result, dest, flag) = *b.mux_multi(&cases, b.lit((0, REG_NONE, false)));

    let mut regs = Vec::with_capacity(s1.regs.len());
    for (i, &v_old) in s1.regs.iter().enumerate() {
        let is_dest = b.eq(b.lit(i as u8), dest);
        regs.push(b.mux(is_dest, result, v_old));
    }

    let pc_is_dest = b.eq(b.lit(REG_PC), dest);
    let pc = b.mux(pc_is_dest, result, b.add(s1.pc, b.lit(1)));

    let s2 = RamStateRepr{pc, regs, flag};
    let im = CalcIntermediate{x,y, result, mem_port};
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

    wire_assert!(
        cx, b.eq(trace_s.flag, calc_s.flag),
        "cycle {} sets flag to {} (expected {})",
        cycle, cx.eval(trace_s.flag), cx.eval(calc_s.flag),
    );
}

fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_ports: &[TWire<'a, MemPort>],
    calc_im: &CalcIntermediate<'a>,
) {
    let _g = b.scoped_label(format_args!("check_step/cycle {}", cycle));

    let has_mem_port = mem_ports.iter().fold(
        b.lit(false),
        |acc, port| b.or(acc, b.eq(port.cycle, b.lit(cycle))),
    );

    let x = calc_im.x;
    let y = calc_im.y;
    let result = calc_im.result;
    let mem_port = calc_im.mem_port;

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
            cx, b.eq(mem_port.cycle, b.lit(cycle)),
            "cycle {}'s mem port has bad cycle number {}",
            cycle, cx.eval(mem_port.cycle),
        );
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

    // Non-memory ops must not use a memory port.  This prevents a malicious prover from
    // introducing fake stores on non-store instructions.
    wire_assert!(
        cx, b.eq(has_mem_port, is_mem),
        "cycle {} mem port usage is {} (expected {})",
        cycle, cx.eval(has_mem_port), cx.eval(is_mem),
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
    wire_assert!(
        cx, b.not(s.flag),
        "initial flag is {} (expected {})",
        cx.eval(s.flag), 0,
    );
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

fn check_first_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    port: &TWire<'a, MemPort>,
) {
    let _g = b.scoped_label("check_first_mem");
    // If the first memory port is active, then it must not be a read, since there are no previous
    // writes to read from.
    let active = b.ne(port.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));
    wire_bug_if!(
        cx, b.mux(active, b.eq(port.op, b.lit(MemOpKind::Read)), b.lit(false)),
        "uninit read from {:x} on cycle {}",
        cx.eval(port.addr), cx.eval(port.cycle),
    );
}

/// Check that memory operation `port2` can follow operation `port1`.
fn check_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    index: usize,
    port1: &TWire<'a, MemPort>,
    port2: &TWire<'a, MemPort>,
) {
    let _g = b.scoped_label(format_args!("check_mem/index {}", index));
    let active = b.ne(port2.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));

    // Whether `port2` is the first memory op for its address.
    let is_first = b.or(
        b.ne(port1.addr, port2.addr),
        b.eq(port1.cycle, b.lit(MEM_PORT_UNUSED_CYCLE)),
    );

    cx.when(b, b.and(active, b.not(is_first)), |cx| {
        cx.when(b, b.eq(port1.op, b.lit(MemOpKind::Poison)), |cx| {
            let is_poison = b.eq(port2.op, b.lit(MemOpKind::Poison));

            // Poison -> Poison is invalid.
            wire_assert!(
                cx, b.not(is_poison),
                "double poison of address {:x} on cycle {}",
                cx.eval(port2.addr), cx.eval(port2.cycle),
            );

            // Poison -> Read/Write is a bug.
            wire_bug_if!(
                cx, b.not(is_poison),
                "access of poisoned address {:x} on cycle {}",
                cx.eval(port2.addr), cx.eval(port2.cycle),
            );
        });

        // A Read must have the same value as the previous Read/Write.  (Write and Poison values
        // are unconstrained.)
        cx.when(b, b.eq(port2.op, b.lit(MemOpKind::Read)), |cx| {
            wire_assert!(
                cx, b.eq(port1.value, port2.value),
                "read from {:x} on cycle {} produced {} (expected {})",
                cx.eval(port2.addr), cx.eval(port2.cycle),
                cx.eval(port2.value), cx.eval(port1.value),
            );
        });
    });

    cx.when(b, b.and(active, is_first), |cx| {
        // The first operation for an address can't be a Read, since there is no previous Write for
        // it to read from.
        wire_assert!(
            cx, b.ne(port2.op, b.lit(MemOpKind::Read)),
            "uninit read from {:x} on cycle {}",
            cx.eval(port2.addr), cx.eval(port2.cycle),
        );
    });
}

fn check_first_fetch<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    port: &TWire<'a, FetchPort>,
) {
    let _g = b.scoped_label("check_first_fetch");
    wire_assert!(
        cx, port.write,
        "uninit fetch from program address {:x}",
        cx.eval(port.addr),
    );
}

fn check_fetch<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    index: usize,
    port1: &TWire<'a, FetchPort>,
    port2: &TWire<'a, FetchPort>,
) {
    let _g = b.scoped_label(format_args!("check_fetch/index {}", index));
    cx.when(b, b.not(port2.write), |cx| {
        wire_assert!(
            cx, b.eq(port2.addr, port1.addr),
            "fetch from uninitialized program address {:x}",
            cx.eval(port2.addr),
        );
        wire_assert!(
            cx, b.eq(port2.instr, port1.instr),
            "fetch from program address {:x} produced wrong instruction",
            cx.eval(port2.addr),
        );
    });
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
                let wires = run_pass(&c, wires, f);
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
    let exec: Execution = match trace_path.extension().and_then(|os| os.to_str()) {
        Some("yaml") => serde_yaml::from_slice(&content).unwrap(),
        Some("cbor") => serde_cbor::from_slice(&content).unwrap(),
        Some("json") => serde_json::from_slice(&content).unwrap(),
        _ => serde_cbor::from_slice(&content).unwrap(),
    };

    let mut trace = Vec::new();
    for (i, state) in exec.trace.iter().enumerate() {
        let _g = b.scoped_label(format_args!("state {}", i));
        trace.push(RamState::secret_with_value(&b, state.clone()));
    }

    let mut mem_ports: Vec<TWire<MemPort>> = Vec::new();
    let mut advices = HashMap::new();
    for i in 1..trace.len() {
        mem_ports.push(b.secret(Some(MemPort {
            // We want all in-use `MemPort`s to be distinct, since it simplifies checking the
            // correspondence between `MemPort`s and steps.  We make unused ports distinct too, so
            // we can just check that all ports are distinct.
            addr: i as u64,
            cycle: MEM_PORT_UNUSED_CYCLE,
            ..MemPort::default()
        })));
    }
    for (&i, advs) in &exec.advice {
        for adv in advs {
            match *adv {
                Advice::MemOp { addr, value, op } => {
                    // It should be fine to replace the old `Secret` gates with new ones here.  The
                    // shape of the circuit will be the same either way.
                    mem_ports[i as usize - 1] = b.secret(Some(MemPort {
                        cycle: i as u32 - 1,
                        addr, value, op,
                    }));
                },
                Advice::Stutter => {},
                Advice::Advise { advise } => {
                    advices.insert(i as u32 - 1, advise);
                },
            }
        }
    }
    for seg in &exec.init_mem {
        for i in 0 .. seg.len {
            let x = seg.data.get(i as usize).cloned().unwrap_or(0);
            let mp = MemPort {
                cycle: MEM_PORT_PRELOAD_CYCLE,
                addr: seg.start + i as u64,
                value: x,
                op: MemOpKind::Write,
            };
            let wire = if seg.secret { b.secret(Some(mp)) } else { b.lit(mp) };
            mem_ports.push(wire);
        }
    }

    let mut fetch_ports: Vec<TWire<FetchPort>> = Vec::new();
    for (i, x) in exec.program.iter().enumerate() {
        fetch_ports.push(b.secret(Some(FetchPort {
            addr: i as u64,
            instr: *x,
            write: true,
        })));
    }
    for s in &exec.trace[..exec.trace.len() - 1] {
        let idx = s.pc as usize;
        assert!(
            idx < exec.program.len(),
            "program executes out of bounds: {} >= {}", idx, exec.program.len(),
        );
        fetch_ports.push(b.secret(Some(FetchPort {
            addr: s.pc,
            instr: exec.program[s.pc as usize],
            write: false,
        })));
    }

    // Generate IR code to check the trace

    check_first(&cx, &b, trace.first().unwrap());

    let check_steps = args.value_of("check-steps").and_then(|c| c.parse().ok()).map(|c| if c <= 0 {1} else {c}).unwrap_or(1);
    let mut prev_s = trace[0].clone();
    for (i, s2) in trace.iter().skip(1).enumerate() {
        let instr = b.with_label(format_args!("cycle {} instr", i), || {
            b.secret(Some(exec.program[exec.trace[i].pc as usize]))
        });
        let port = &mem_ports[i];
        let advice = b.secret(Some(*advices.get(&(i as u32)).unwrap_or(&0)));
        let (calc_s, calc_im) = calc_step(&b, i as u32, instr, &[port.clone()], advice, &prev_s);

        // Check trace every D steps. 
        if i % check_steps == 0 {
            check_state(&cx, &b, i as u32, &calc_s, s2);
            prev_s = s2.clone();
        }
        else {
            // TODO: Drop this pc check once `FetchPort` is refactored.
            wire_assert!(
                &cx, b.eq(s2.pc, calc_s.pc),
                "cycle {} sets pc to {} (expected {})",
                i, cx.eval(s2.pc), cx.eval(calc_s.pc),
            );

            prev_s = calc_s.clone();
        }
        check_step(&cx, &b, i as u32, instr, &[port.clone()], &calc_im);
    }

    check_last(&cx, &b, trace.last().unwrap(), args.is_present("expect-zero"));

    // Check the memory ports
    for (i, port) in mem_ports.iter().enumerate().take(trace.len() - 1) {
        // Currently, ports have a 1-to-1 mapping to steps.  We check that either the port is used
        // in its corresponding cycle, or it isn't used at all.
        wire_assert!(
            &cx,
            b.or(
                b.eq(port.cycle, b.lit(i as u32)),
                b.eq(port.cycle, b.lit(MEM_PORT_UNUSED_CYCLE)),
            ),
            "port {} is active on cycle {} (expected {})",
            i, cx.eval(port.cycle), i,
        );
    }

    // Check memory consistency

    let sorted_mem = {
        let _g = b.scoped_label("sort mem");
        let mut packed = mem_ports.iter().map(|&fp| {
            PackedMemPort::from_unpacked(&b, fp)
        }).collect::<Vec<_>>();
        // Using `lt` instead of `le` for the comparison here means the sortedness check will also
        // ensure that every `MemPort` is distinct.
        let sorted = sort::sort(&b, &mut packed, &mut |&x, &y| b.lt(x, y));
        wire_assert!(&cx, sorted, "memory op sorting failed");
        packed.iter().map(|pmp| pmp.unpack(&b)).collect::<Vec<_>>()
    };
    trace!("mem ops:");
    for (i, port) in mem_ports.iter().enumerate() {
        trace!(
            "mem op {:3}: op{}, {:x}, value {}, cycle {}",
            i, cx.eval(port.op.repr), cx.eval(port.addr), cx.eval(port.value), cx.eval(port.cycle),
        );
    }
    trace!("sorted mem ops:");
    for (i, port) in sorted_mem.iter().enumerate() {
        trace!(
            "mem op {:3}: op{}, {:x}, value {}, cycle {}",
            i, cx.eval(port.op.repr), cx.eval(port.addr), cx.eval(port.value), cx.eval(port.cycle),
        );
    }
    check_first_mem(&cx, &b, &sorted_mem[0]);
    for (i, (port1, port2)) in sorted_mem.iter().zip(sorted_mem.iter().skip(1)).enumerate() {
        check_mem(&cx, &b, i, port1, port2);
    }

    // Check instruction-fetch consistency

    let sorted_fetch = {
        let _g = b.scoped_label("sort fetch");
        let mut packed = fetch_ports.iter().map(|&fp| {
            PackedFetchPort::from_unpacked(&b, fp)
        }).collect::<Vec<_>>();
        let sorted = sort::sort(&b, &mut packed, &mut |&x, &y| b.le(x, y));
        wire_assert!(&cx, sorted, "instruction fetch sorting failed");
        packed.iter().map(|pfp| pfp.unpack(&b)).collect::<Vec<_>>()
    };
    trace!("fetches:");
    for (i, port) in fetch_ports.iter().enumerate() {
        trace!(
            "fetch {:3}: {:5} {:x}, op{} {} {} {} {}",
            i, cx.eval(port.write).0.map_or("??", |x| if x == 0 { "read" } else { "write" }),
            cx.eval(port.addr), cx.eval(port.instr.opcode), cx.eval(port.instr.dest),
            cx.eval(port.instr.op1), cx.eval(port.instr.op2), cx.eval(port.instr.imm),
        );
    }
    trace!("sorted fetches:");
    for (i, port) in sorted_fetch.iter().enumerate() {
        trace!(
            "fetch {:3}: {:5} {:x}, op{} {} {} {} {}",
            i, cx.eval(port.write).0.map_or("??", |x| if x == 0 { "read" } else { "write" }),
            cx.eval(port.addr), cx.eval(port.instr.opcode), cx.eval(port.instr.dest),
            cx.eval(port.instr.op1), cx.eval(port.instr.op2), cx.eval(port.instr.imm),
        );
    }
    check_first_fetch(&cx, &b, &sorted_fetch[0]);
    for (i, (port1, port2)) in sorted_fetch.iter().zip(sorted_fetch.iter().skip(1)).enumerate() {
        check_fetch(&cx, &b, i, port1, port2);
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
