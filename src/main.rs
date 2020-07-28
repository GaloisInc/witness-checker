use std::env;
use std::fs::{self, File};
use std::io::{self, BufWriter};
use bumpalo::Bump;

use cheesecloth::back;
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::gadget::arith::BuilderExt as _;
use cheesecloth::lower::{self, run_pass};
use cheesecloth::parse;
use cheesecloth::tiny_ram::{RamInstr, RamState, MemPort, Opcode, REG_NONE, REG_PC};

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
    b: &Builder<'a>,
    cycle: u64,
    prog: &[TWire<'a, RamInstr>],
    mem_ports: &[TWire<'a, MemPort>],
    s1: &TWire<'a, RamState>,
    s2: &TWire<'a, RamState>,
) -> Vec<TWire<'a, bool>> {
    let instr = b.index(prog, s1.pc, |b, i| b.lit(i as u64));

    let mut cases = Vec::new();
    let mut add_case = |op, result, dest, flag| {
        let op_match = b.eq(b.lit(op as u8), instr.opcode);
        let parts = TWire::<(_, _, _)>::new((result, dest, flag));
        cases.push(TWire::<(_, _)>::new((op_match, parts)));
    };

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u64));
    let y = operand_value(b, s1, instr.op2, instr.imm);

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

    let mut ok = Vec::new();
    for (i, (&v_old, &v_new)) in s1.regs.iter().zip(s2.regs.iter()).enumerate() {
        let is_dest = b.eq(b.lit(i as u64), dest);
        let expect_new = b.mux(is_dest, result, v_old);
        let new_ok = b.eq(v_new, expect_new);
        ok.push(new_ok);
    }

    let pc_is_dest = b.eq(b.lit(REG_PC), dest);
    let expect_pc = b.mux(pc_is_dest, result, b.add(s1.pc, b.lit(1)));
    ok.push(b.eq(s2.pc, expect_pc));

    ok.push(b.eq(s2.flag, expect_flag));


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
    ok.push(b.mux(is_mem, cycle_ok, b.lit(true)));
    ok.push(b.mux(is_mem, addr_ok, b.lit(true)));
    ok.push(b.mux(is_load, load_value_ok, b.lit(true)));
    ok.push(b.mux(is_store, store_value_ok, b.lit(true)));
    ok.push(b.mux(is_mem, store_ok, b.lit(true)));


    ok
}

fn check_first<'a>(
    b: &Builder<'a>,
    _prog: &[TWire<'a, RamInstr>],
    s: &TWire<'a, RamState>,
) -> Vec<TWire<'a, bool>> {
    let mut ok = Vec::new();
    ok.push(b.eq(s.pc, b.lit(0)));
    for &r in s.regs.iter().skip(1) {
        ok.push(b.eq(r, b.lit(0)));
    }
    ok.push(b.not(s.flag));
    ok
}

fn check_last<'a>(
    b: &Builder<'a>,
    prog: &[TWire<'a, RamInstr>],
    s: &TWire<'a, RamState>,
) -> Vec<TWire<'a, bool>> {
    let pc_ok = b.eq(s.pc, b.lit(prog.len() as u64));
    let r0_ok = b.eq(s.regs[0], b.lit(0));
    vec![pc_ok, r0_ok]
}

fn main() -> io::Result<()> {
    let args = env::args().collect::<Vec<_>>();
    assert!(args.len() == 3, "usage: {} PROGRAM TRACE", args.get(0).map_or("witness-checker", |x| x));
    let arena = Bump::new();
    let b = Builder::new(&arena);

    // Load the program and trace from files
    let mut prog = Vec::new();
    let prog_str = fs::read_to_string(&args[1]).unwrap();
    for line in prog_str.lines() {
        prog.push(b.lit(parse::parse_instr(line)));
    }

    let mut trace = Vec::new();
    let trace_str = fs::read_to_string(&args[2]).unwrap();
    for line in trace_str.lines() {
        trace.push(b.secret(Some(parse::parse_state(line))));
    }

    // Generate IR code to check the trace
    let mut ok = Vec::new();

    ok.append(&mut check_first(&b, &prog, trace.first().unwrap()));

    for (i, (s1, s2)) in trace.iter().zip(trace.iter().skip(1)).enumerate() {
        ok.append(&mut check_step(&b, i as u64, &prog, &[], s1, s2));
    }

    ok.append(&mut check_last(&b, &prog, trace.last().unwrap()));

    // Lower IR code
    let c = b.finish();

    let ok = ok.into_iter().map(|tw| tw.repr).collect::<Vec<_>>();
    // TODO: need a better way to handle passes that must be run to fixpoint
    let ok = run_pass(&c, ok, lower::gadget::decompose_all_gadgets);
    let ok = run_pass(&c, ok, lower::gadget::decompose_all_gadgets);
    let ok = run_pass(&c, ok, lower::bundle::unbundle_mux);
    let ok = run_pass(&c, ok, lower::bundle::simplify);
    let ok = run_pass(&c, ok, lower::int::mod_to_div);
    let ok = run_pass(&c, ok, lower::int::non_constant_shift);
    let ok = run_pass(&c, ok, lower::int::extend_to_64);
    let ok = run_pass(&c, ok, lower::int::int_to_uint);
    let ok = run_pass(&c, ok, lower::int::reduce_lit_32);
    let ok = run_pass(&c, ok, lower::int::mux);
    let ok = run_pass(&c, ok, lower::int::compare_to_zero);
    let ok = run_pass(&c, ok, lower::bool_::mux);
    let ok = run_pass(&c, ok, lower::bool_::compare_to_logic);
    let ok = run_pass(&c, ok, lower::bool_::not_to_xor);

    // Generate SCALE
    let mut backend = back::scale::Backend::new();
    backend.print_str("results: ");
    for w in ok {
        let sbit = backend.wire(w);
        let bit = backend.reveal(sbit);
        backend.print(bit);
    }
    backend.print_str("\n");


    // Write out the generated SCALE program
    let instrs = backend.finish();
    let mut f = BufWriter::new(File::create("out.bc")?);
    for i in instrs {
        scale_isa::functions::write_instruction(&mut f, i)?;
    }

    Ok(())
}
