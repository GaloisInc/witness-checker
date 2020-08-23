use std::cell::RefCell;
use std::env;
use std::fs::{self, File, remove_file};
use std::io::{self, BufWriter};
use std::path::Path;
use bumpalo::Bump;

use cheesecloth::back;
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::gadget::arith::BuilderExt as _;
use cheesecloth::lower::{self, run_pass};
use cheesecloth::sort;
use cheesecloth::tiny_ram::{Execution, RamInstr, RamState, MemPort, Opcode, REG_NONE, REG_PC};
use zkinterface::Messages;

struct Context<'a> {
    asserts: RefCell<Vec<TWire<'a, bool>>>,
    bugs: RefCell<Vec<TWire<'a, bool>>>,
}

impl<'a> Context<'a> {
    fn new() -> Context<'a> {
        Context {
            asserts: RefCell::new(Vec::new()),
            bugs: RefCell::new(Vec::new()),
        }
    }

    fn finish(self) -> (Vec<TWire<'a, bool>>, Vec<TWire<'a, bool>>) {
        (
            self.asserts.into_inner(),
            self.bugs.into_inner(),
        )
    }

    /// Mark the execution as invalid if `cond` is false.  A failed assertion represents
    /// misbehavior on the part of the prover.
    fn assert(&self, cond: TWire<'a, bool>) {
        self.asserts.borrow_mut().push(cond);
    }

    /// Signal an error condition of `cond` is true.  This should be used for situations like
    /// buffer overflows, which indicate a bug in the subject program.
    fn bug_if(&self, cond: TWire<'a, bool>) {
        self.bugs.borrow_mut().push(cond);
    }

    fn when<R>(
        &self,
        b: &Builder<'a>,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_>) -> R,
    ) -> R {
        f(&ContextWhen { cx: self, b, path_cond })
    }
}

struct ContextWhen<'a, 'b> {
    cx: &'b Context<'a>,
    b: &'b Builder<'a>,
    path_cond: TWire<'a, bool>,
}

impl<'a, 'b> ContextWhen<'a, 'b> {
    fn assert(&self, cond: TWire<'a, bool>) {
        // The assertion passes if either this `when` block is not taken, or `cond` is satisfied.
        self.cx.assert(self.b.or(self.b.not(self.path_cond), cond));
    }

    fn bug_if(&self, cond: TWire<'a, bool>) {
        // The bug occurs if this `when` block is taken and `cond` is satisfied.
        self.cx.bug_if(self.b.and(self.path_cond, cond));
    }

    fn when<R>(
        &self,
        b: &Builder<'a>,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_>) -> R,
    ) -> R {
        self.cx.when(b, b.and(self.path_cond, path_cond), f)
    }
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

fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    prog: &[TWire<'a, RamInstr>],
    mem_ports: &[TWire<'a, MemPort>],
    s1: &TWire<'a, RamState>,
    s2: &TWire<'a, RamState>,
) {
    let instr = b.index(prog, s1.pc, |b, i| b.lit(i as u64));

    let mut cases = Vec::new();
    let mut add_case = |op, result, dest, flag| {
        let op_match = b.eq(b.lit(op as u8), instr.opcode);
        let parts = TWire::<(_, _, _)>::new((result, dest, flag));
        cases.push(TWire::<(_, _)>::new((op_match, parts)));
    };

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u64));
    let y = operand_value(b, s1, instr.op2, instr.imm);

    let has_mem_port = mem_ports.iter().fold(
        b.lit(false),
        |acc, port| b.or(acc, b.eq(port.cycle, b.lit(cycle))),
    );
    let mem_port = b.select(
        mem_ports,
        b.lit(MemPort::default()),
        |port| b.eq(port.cycle, b.lit(cycle)),
    );

    {
        let result = b.and(x, y);
        add_case(Opcode::And, result, instr.dest, b.eq(result, b.lit(0)));
    }

    {
        let result = b.or(x, y);
        add_case(Opcode::Or, result, instr.dest, b.eq(result, b.lit(0)));
    }

    {
        let result = b.xor(x, y);
        add_case(Opcode::Xor, result, instr.dest, b.eq(result, b.lit(0)));
    }

    {
        let result = b.not(y);
        add_case(Opcode::Not, result, instr.dest, b.eq(result, b.lit(0)));
    }

    {
        let (result, overflow) = b.add_with_overflow(x, y);
        add_case(Opcode::Add, result, instr.dest, overflow);
    }

    {
        let (result, overflow) = b.sub_with_overflow(x, y);
        add_case(Opcode::Sub, result, instr.dest, overflow);
    }

    {
        let (low, high) = *b.wide_mul(x, y);
        add_case(Opcode::Mull, low, instr.dest, b.ne(high, b.lit(0)));
    }

    {
        let (_, high) = *b.wide_mul(x, y);
        add_case(Opcode::Umulh, high, instr.dest, b.ne(high, b.lit(0)));
    }

    {
        let (_, high_s) = *b.wide_mul(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        // TODO: not sure this gives the right overflow value - what if high = -1?
        add_case(Opcode::Smulh, b.cast::<_, u64>(high_s), instr.dest, b.ne(high_s, b.lit(0)));
    }

    {
        let result = b.div(x, y);
        add_case(Opcode::Udiv, result, instr.dest, b.eq(y, b.lit(0)));
    }

    {
        let result = b.mod_(x, y);
        add_case(Opcode::Umod, result, instr.dest, b.eq(y, b.lit(0)));
    }

    {
        let result = b.shl(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shl, result, instr.dest, b.ne(b.and(y, b.lit(1 << 63)), b.lit(0)));
    }

    {
        let result = b.shr(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shr, result, instr.dest, b.ne(b.and(y, b.lit(1)), b.lit(0)));
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

    let (result, dest, expect_flag) = *b.mux_multi(&cases, b.lit((0, REG_NONE, false)));

    for (i, (&v_old, &v_new)) in s1.regs.iter().zip(s2.regs.iter()).enumerate() {
        let is_dest = b.eq(b.lit(i as u64), dest);
        let expect_new = b.mux(is_dest, result, v_old);
        cx.assert(b.eq(v_new, expect_new));
    }

    let pc_is_dest = b.eq(b.lit(REG_PC), dest);
    let expect_pc = b.mux(pc_is_dest, result, b.add(s1.pc, b.lit(1)));
    cx.assert(b.eq(s2.pc, expect_pc));

    cx.assert(b.eq(s2.flag, expect_flag));


    // If the instruction is a store or a load, we need additional checks to make sure the fields
    // of `mem_port` match the instruction operands.
    let is_load = b.eq(instr.opcode, b.lit(Opcode::Load as u8));
    let is_store = b.eq(instr.opcode, b.lit(Opcode::Store as u8));
    let is_mem = b.or(is_load, is_store);

    // TODO: shouldn't need an extra `eq` here
    let cycle_ok = b.eq(mem_port.cycle, b.lit(cycle));
    let addr_ok = b.eq(mem_port.addr, y);
    let load_value_ok = b.eq(mem_port.value, result);
    let store_value_ok = b.eq(mem_port.value, x);
    let store_ok = b.eq(mem_port.write, is_store);
    cx.assert(b.mux(is_mem, cycle_ok, b.lit(true)));
    cx.assert(b.mux(is_mem, addr_ok, b.lit(true)));
    cx.assert(b.mux(is_load, load_value_ok, b.lit(true)));
    cx.assert(b.mux(is_store, store_value_ok, b.lit(true)));
    cx.assert(b.mux(is_mem, store_ok, b.lit(true)));

    // Non-memory ops must not use a memory port.  This prevents a malicious prover from
    // introducing fake stores on non-store instructions.
    cx.assert(b.eq(has_mem_port, is_mem));
}

fn check_first<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    _prog: &[TWire<'a, RamInstr>],
    s: &TWire<'a, RamState>,
) {
    cx.assert(b.eq(s.pc, b.lit(0)));
    for &r in s.regs.iter().skip(1) {
        cx.assert(b.eq(r, b.lit(0)));
    }
    cx.assert(b.not(s.flag));
}

fn check_last<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    prog: &[TWire<'a, RamInstr>],
    s: &TWire<'a, RamState>,
) {
    cx.assert(b.eq(s.pc, b.lit(prog.len() as u64)));
    cx.assert(b.eq(s.regs[0], b.lit(0)));
}

fn check_first_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    port: &TWire<'a, MemPort>,
) {
    // If the first memory port is active, then it must be a write, since there are no previous
    // writes to read from.
    let active = b.ne(port.cycle, b.lit(!0));
    cx.bug_if(b.mux(active, b.not(port.write), b.lit(false)));
}

fn check_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    port1: &TWire<'a, MemPort>,
    port2: &TWire<'a, MemPort>,
) {
    let active = b.and(b.ne(port1.cycle, b.lit(!0)), b.ne(port2.cycle, b.lit(!0)));

    cx.when(b, active, |cx| {
        cx.when(b, b.not(port2.write), |cx| {
            // `port2` is a read.

            // `port1` should be a read or write with the same address.  Otherwise, `port2` is a
            // read from uninitialized memory.
            let is_init = b.eq(port1.addr, port2.addr);
            cx.bug_if(b.not(is_init));

            // If this is a legal read, then it must return the same value as the previous
            // operation.  Otherwise, the prover is cheating by changing memory without a proper
            // write.
            cx.when(b, is_init, |cx| cx.assert(b.eq(port1.value, port2.value)));
        });

        // If `port2` is a write, then its address and value are unconstrained.
    });
}

fn main() -> io::Result<()> {
    let args = env::args().collect::<Vec<_>>();
    assert!(args.len() == 2, "usage: {} WITNESS", args.get(0).map_or("witness-checker", |x| x));
    let arena = Bump::new();
    let b = Builder::new(&arena);
    let cx = Context::new();

    // Load the program and trace from files
    let content = fs::read(&args[1]).unwrap();
    let exec: Execution = match Path::new(&args[1]).extension().and_then(|os| os.to_str()) {
        Some("yaml") => serde_yaml::from_slice(&content).unwrap(),
        Some("cbor") => serde_cbor::from_slice(&content).unwrap(),
        Some("json") => serde_json::from_slice(&content).unwrap(),
        _ => serde_cbor::from_slice(&content).unwrap(),
    };

    let mut prog = Vec::new();
    for instr in exec.program {
        prog.push(b.lit(instr));
    }

    let mut trace = Vec::new();
    for state in exec.trace {
        trace.push(RamState::secret_with_value(&b, state));
    }

    let mut mem_ports = Vec::new();
    for _ in 1..trace.len() {
        mem_ports.push(b.secret(Some(MemPort {
            cycle: !0,
            ..MemPort::default()
        })));
    }

    // Generate IR code to check the trace

    check_first(&cx, &b, &prog, trace.first().unwrap());

    for (i, (s1, s2)) in trace.iter().zip(trace.iter().skip(1)).enumerate() {
        let port = &mem_ports[i];
        check_step(&cx, &b, i as u32, &prog, &[port.clone()], s1, s2);
    }

    check_last(&cx, &b, &prog, trace.last().unwrap());

    // Check the memory ports
    for (i, port) in mem_ports.iter().enumerate() {
        // Currently, ports have a 1-to-1 mapping to steps.  We check that either the port is used
        // in its corresponding cycle, or it isn't used at all.
        cx.assert(b.or(
            b.eq(port.cycle, b.lit(i as u32)),
            b.eq(port.cycle, b.lit(!0_u32)),
        ));
    }

    // Check memory consistency
    let mut sorted_mem = mem_ports.clone();
    sort::sort(&b, &mut sorted_mem, &mut |x, y| {
        b.or(
            b.lt(x.addr, y.addr),
            b.and(b.eq(x.addr, y.addr), b.lt(x.cycle, y.cycle)),
        )
    });
    check_first_mem(&cx, &b, &sorted_mem[0]);
    for (port1, port2) in sorted_mem.iter().zip(sorted_mem.iter().skip(1)) {
        check_mem(&cx, &b, port1, port2);
    }

    // Lower IR code
    let c = b.finish();

    let (asserts, bugs) = cx.finish();
    let num_asserts = asserts.len();
    let flags = asserts.into_iter().chain(bugs.into_iter())
        .map(|tw| tw.repr).collect::<Vec<_>>();

    // TODO: need a better way to handle passes that must be run to fixpoint
    let flags = run_pass(&c, flags, lower::gadget::decompose_all_gadgets);
    let flags = run_pass(&c, flags, lower::gadget::decompose_all_gadgets);
    let flags = run_pass(&c, flags, lower::bundle::unbundle_mux);
    let flags = run_pass(&c, flags, lower::bundle::simplify);
    let flags = run_pass(&c, flags, lower::const_fold::const_fold);
    let flags = run_pass(&c, flags, lower::int::mod_to_div);
    let flags = run_pass(&c, flags, lower::int::non_constant_shift);
    let flags = run_pass(&c, flags, lower::int::extend_to_64);
    let flags = run_pass(&c, flags, lower::int::int_to_uint);
    let flags = run_pass(&c, flags, lower::int::reduce_lit_32);
    let flags = run_pass(&c, flags, lower::int::mux);
    let flags = run_pass(&c, flags, lower::int::compare_to_zero);
    let flags = run_pass(&c, flags, lower::bool_::mux);
    let flags = run_pass(&c, flags, lower::bool_::compare_to_logic);
    let flags = run_pass(&c, flags, lower::bool_::not_to_xor);

    // Print
    for wire in &flags {
        //println!("Wire {:?}", wire);
    }

    #[cfg(feature = "bellman")] {
        // Clean workspace.
        let workspace = Path::new("local/test");
        let files = vec![
            workspace.join("main.zkif"),
            workspace.join("constraints.zkif"),
            workspace.join("witness.zkif"),
        ];
        for f in &files {
            let _ = remove_file(f);
        }

        // Generate the circuit and witness.
        let mut backend = back::zkif::backend::Backend::new(workspace, true);
        for flag in &flags {
            backend.wire(*flag);
        }
        // Write files.
        drop(backend);

        // Validate the circuit and witness.
        let mut messages = Messages::new();
        for f in &files {
            messages.read_file(f).unwrap();
        }
        zkinterface_bellman::zkif_backend::validate(&messages, false).unwrap();

        // TODO: Compact all output wires into an assertion.
    }

    #[cfg(feature = "scale")] {
        // Generate SCALE
        let mut backend = back::scale::Backend::new();

        backend.print_str("asserts: ");
        for w in flags.iter().take(num_asserts) {
            let sbit = backend.wire(w.clone());
            let bit = backend.reveal(sbit);
            backend.print(bit);
        }
        backend.print_str("\n");

        backend.print_str("bugs: ");
        for w in flags.iter().skip(num_asserts) {
            let sbit = backend.wire(w.clone());
            let bit = backend.reveal(sbit);
            backend.print(bit);
        }

        // Write out the generated SCALE program
        let instrs = backend.finish();
        let mut f = BufWriter::new(File::create("out.bc")?);
        for i in instrs {
            scale_isa::functions::write_instruction(&mut f, i)?;
        }
    }

    Ok(())
}
