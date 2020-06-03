use std::fs::File;
use std::io::{self, BufWriter};
use scale_isa;
use scale_isa::types::{RegSecretRegint, RegSecretBit};

use cheesecloth::builder::Builder;
use cheesecloth::tiny_ram::{RamInstr, RamState, Opcode, RAM_REGS};

fn operand_value(
    b: &mut Builder,
    s: &RamState,
    op: RegSecretRegint,
    imm: RegSecretBit,
) -> RegSecretRegint {
    let reg_val = b.index(&s.regs, op);
    b.mux(imm, op, reg_val)
}

fn check_step(b: &mut Builder, prog: &[RamInstr], s1: &RamState, s2: &RamState) -> Vec<RegSecretBit> {
    let instr = b.index(prog, s1.pc);
    let false_ = b.ld(0);
    b.match_(
        instr.opcode,
        Opcode::iter().map(|i| i as usize),
        vec![false_; RAM_REGS],
        |b, i| {
            let result = match Opcode::from_raw(i as u8) {
                Opcode::Mov => {
                    operand_value(b, s1, instr.op1, instr.imm)
                },
                Opcode::Add => {
                    let x = b.index(&s1.regs, instr.op1);
                    let y = operand_value(b, s1, instr.op2, instr.imm);
                    b.add(x, y)
                },
                Opcode::Sub => {
                    let x = b.index(&s1.regs, instr.op1);
                    let y = operand_value(b, s1, instr.op2, instr.imm);
                    b.sub(x, y)
                },
                Opcode::Mull => {
                    let x = b.index(&s1.regs, instr.op1);
                    let y = operand_value(b, s1, instr.op2, instr.imm);
                    b.mul(x, y)
                },
            };

            let mut ok = Vec::new();
            for (i, (&v_old, &v_new)) in s1.regs.iter().zip(s2.regs.iter()).enumerate() {
                let i_val = b.ld(i as u32);
                let is_dest = b.eq(i_val, instr.dest);
                let expect_new = b.mux(is_dest, result, v_old);
                let new_ok = b.eq(v_new, expect_new);
                ok.push(new_ok);
            }
            ok
        },
    )
}

fn check_first(b: &mut Builder, prog: &[RamInstr], s: &RamState) -> Vec<RegSecretBit> {
    let mut ok = Vec::new();
    let expect_pc = b.ld(0);
    ok.push(b.eq(s.pc, expect_pc));
    for &r in s.regs.iter().skip(1) {
        let expect_val = b.ld(0);
        ok.push(b.eq(r, expect_val));
    }
    ok.push(b.not(s.flag));
    ok
}

fn check_last(b: &mut Builder, prog: &[RamInstr], s: &RamState) -> Vec<RegSecretBit> {
    let expect_pc = b.ld(prog.len() as u32);
    let pc_ok = b.eq(s.pc, expect_pc);
    let expect_r0 = b.ld(0);
    let r0_ok = b.eq(s.regs[0], expect_r0);
    vec![pc_ok, r0_ok]
}

fn main() -> io::Result<()> {
    let mut b = Builder::default();

    {
        let prog = vec![
            RamInstr::mull(&mut b, 2, 0, 0),        // r2 = r0 * r0 (x^2)
            RamInstr::mull_imm(&mut b, 1, 0, 3),    // r1 = 3 * r0 (3x)
            RamInstr::add(&mut b, 0, 1, 2),         // r0 = r1 + r2 (x^2 + 3x)
            RamInstr::sub_imm(&mut b, 0, 0, 10),    // r0 = r0 - 10 (x^2 + 3x - 10)
        ];

        let trace = vec![
            RamState::new(&mut b, 0, [2, 0, 0], false),
            RamState::new(&mut b, 1, [2, 0, 4], false),
            RamState::new(&mut b, 2, [2, 6, 4], false),
            RamState::new(&mut b, 3, [10, 6, 4], false),
            RamState::new(&mut b, 4, [0, 6, 4], false),
        ];

        let mut ok = Vec::new();

        ok.append(&mut check_first(&mut b, &prog, trace.first().unwrap()));

        for (s1, s2) in trace.iter().zip(trace.iter().skip(1)) {
            ok.append(&mut check_step(&mut b, &prog, s1, s2));
        }

        ok.append(&mut check_last(&mut b, &prog, trace.last().unwrap()));

        for sb in ok {
            let sr = b.sb_to_sr(sb);
            let clear = b.reveal(sr);
            b.print(clear);
        }
    }

    let instrs = b.finish();
    let mut f = BufWriter::new(File::create("out.bc")?);
    for i in instrs {
        scale_isa::functions::write_instruction(&mut f, i)?;
    }

    Ok(())
}
