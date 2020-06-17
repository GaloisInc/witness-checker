use std::env;
use std::fs::{self, File};
use std::io::{self, BufWriter};
use bumpalo::Bump;

use cheesecloth::back;
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::lower::{self, run_pass};
use cheesecloth::parse;
use cheesecloth::tiny_ram::{RamInstr, RamState, Opcode};

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
    prog: &[TWire<'a, RamInstr>],
    s1: &TWire<'a, RamState>,
    s2: &TWire<'a, RamState>,
) -> Vec<TWire<'a, bool>> {
    let instr = b.index(prog, s1.pc, |b, i| b.lit(i as u64));

    let mut cases = Vec::new();
    let mut add_case = |op, result| {
        let op_match = b.eq(b.lit(op as u64), instr.opcode);
        cases.push(TWire::<(_, _)>::new((op_match, result)));
    };

    {
        let result = operand_value(b, s1, instr.op1, instr.imm);
        add_case(Opcode::Mov, result);
    }

    {
        let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u64));
        let y = operand_value(b, s1, instr.op2, instr.imm);
        add_case(Opcode::Add, b.add(x, y));
    }

    {
        let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u64));
        let y = operand_value(b, s1, instr.op2, instr.imm);
        add_case(Opcode::Sub, b.sub(x, y));
    }

    {
        let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u64));
        let y = operand_value(b, s1, instr.op2, instr.imm);
        add_case(Opcode::Mull, b.mul(x, y));
    }

    let result = b.mux_multi(&cases, b.lit(0));

    let mut ok = Vec::new();
    for (i, (&v_old, &v_new)) in s1.regs.iter().zip(s2.regs.iter()).enumerate() {
        let is_dest = b.eq(b.lit(i as u64), instr.dest);
        let expect_new = b.mux(is_dest, result, v_old);
        let new_ok = b.eq(v_new, expect_new);
        ok.push(new_ok);
    }
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
    let b = Builder::new(&arena, vec![]);

    // Load the program and trace from files
    let mut prog = Vec::new();
    let prog_str = fs::read_to_string(&args[1]).unwrap();
    for line in prog_str.lines() {
        prog.push(b.lit(parse::parse_instr(line)));
    }

    let mut trace = Vec::new();
    let trace_str = fs::read_to_string(&args[2]).unwrap();
    for line in trace_str.lines() {
        trace.push(b.lit(parse::parse_state(line)));
    }

    // Generate IR code to check the trace
    let mut ok = Vec::new();

    ok.append(&mut check_first(&b, &prog, trace.first().unwrap()));

    for (s1, s2) in trace.iter().zip(trace.iter().skip(1)) {
        ok.append(&mut check_step(&b, &prog, s1, s2));
    }

    ok.append(&mut check_last(&b, &prog, trace.last().unwrap()));

    // Lower IR code
    let c = b.finish();

    let ok = ok.into_iter().map(|tw| tw.repr).collect::<Vec<_>>();
    let ok = run_pass(&c, ok, lower::int::mux);
    let ok = run_pass(&c, ok, lower::int::compare_to_zero);
    let ok = run_pass(&c, ok, lower::bool_::mux);
    let ok = run_pass(&c, ok, lower::bool_::compare_to_logic);
    let ok = run_pass(&c, ok, lower::bool_::not_to_xor);

    // Print
    for wire in ok {
        println!("Wire {:?}", wire);
    }

    #[cfg(feature = "scale")] {
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
    }

    Ok(())
}
