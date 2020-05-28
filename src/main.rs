use std::fs::File;
use std::io::{self, BufWriter};
use scale_isa;
use scale_isa::types::{RegClearModp, RegSecretRegint, RegSecretBit};

use cheesecloth::builder::{Builder, Mux};


/// A TinyRAM instruction.  The program itself is not secret, but we most commonly load
/// instructions from secret indices, which results in a secret instruction.
#[derive(Clone, Copy)]
struct RamInstr {
    opcode: RegSecretRegint,
    dest: RegSecretRegint,
    op1: RegSecretRegint,
    op2: RegSecretRegint,
    /// Some opcodes have an operand that can be either a register name or an immediate value.  If
    /// `imm` is set, it's interpreted as an immediate; otherwise, it's a register.
    imm: RegSecretBit,
}

impl RamInstr {
    pub fn new(
        b: &mut Builder,
        opcode: Opcode,
        dest: u32,
        op1: u32,
        op2: u32,
        imm: bool,
    ) -> RamInstr {
        RamInstr {
            opcode: b.ld(opcode as u32),
            dest: b.ld(dest),
            op1: b.ld(op1),
            op2: b.ld(op2),
            imm: b.ld(imm as u32),
        }
    }

    pub fn mov(b: &mut Builder, rd: u32, r1: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Mov, rd, r1, 0, false)
    }

    pub fn mov_imm(b: &mut Builder, rd: u32, imm: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Mov, rd, imm, 0, true)
    }

    pub fn add(b: &mut Builder, rd: u32, r1: u32, r2: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Add, rd, r1, r2, false)
    }

    pub fn add_imm(b: &mut Builder, rd: u32, r1: u32, imm: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Add, rd, r1, imm, true)
    }

    pub fn sub(b: &mut Builder, rd: u32, r1: u32, r2: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Sub, rd, r1, r2, false)
    }

    pub fn sub_imm(b: &mut Builder, rd: u32, r1: u32, imm: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Sub, rd, r1, imm, true)
    }

    pub fn mull(b: &mut Builder, rd: u32, r1: u32, r2: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Mull, rd, r1, r2, false)
    }

    pub fn mull_imm(b: &mut Builder, rd: u32, r1: u32, imm: u32) -> RamInstr {
        RamInstr::new(b, Opcode::Mull, rd, r1, imm, true)
    }
}

impl Mux for RamInstr {
    fn mux(b: &mut Builder, cond: RegSecretBit, then: Self, else_: Self) -> Self {
        RamInstr {
            opcode: b.mux(cond, then.opcode, else_.opcode),
            dest: b.mux(cond, then.dest, else_.dest),
            op1: b.mux(cond, then.op1, else_.op1),
            op2: b.mux(cond, then.op2, else_.op2),
            imm: b.mux(cond, then.imm, else_.imm),
        }
    }
}

const RAM_REGS: usize = 3;

struct RamState {
    pc: RegSecretRegint,
    regs: [RegSecretRegint; RAM_REGS],
    flag: RegSecretBit,
}

impl RamState {
    pub fn new(b: &mut Builder, pc: u32, regs: [u32; RAM_REGS], flag: bool) -> RamState {
        let mut state_regs = [RegSecretRegint::new(0); RAM_REGS];
        for (i, &v) in regs.iter().enumerate() {
            state_regs[i] = b.ld(v);
        }

        RamState {
            pc: b.ld(pc),
            regs: state_regs,
            flag: b.ld(flag as u32),
        }
    }
}

macro_rules! mk_opcode {
    ($($Variant:ident,)*) => {
        #[repr(u8)]
        enum Opcode {
            $($Variant,)*
        }

        impl Opcode {
            fn from_raw(x: u8) -> Opcode {
                let mut y = x;
                $(
                    if y == 0 { return Opcode::$Variant; }
                    y -= 1;
                )*
                panic!("bad value {} for Opcode", x)
            }

            fn count() -> usize {
                0 $(+ { drop(Opcode::$Variant); 1})*
            }

            fn iter() -> impl Iterator<Item = Opcode> {
                (0 .. Self::count() as u8).map(Self::from_raw)
            }
        }
    };
}

mk_opcode! {
    Mov,
    Add,
    Sub,
    Mull,
}

fn check_step(b: &mut Builder, prog: &[RamInstr], s1: &RamState, s2: &RamState) -> RegSecretBit {
    let instr = b.index(prog, s1.pc);
    let false_ = b.ld(0);
    b.match_(
        instr.opcode,
        Opcode::iter().map(|i| i as usize),
        false_,
        |b, i| match Opcode::from_raw(i as u8) {
            Opcode::Mov => {
                b.ld(0)
            },
            Opcode::Add => {
                b.ld(0)
            },
            Opcode::Sub => {
                b.ld(0)
            },
            Opcode::Mull => {
                b.ld(0)
            },
        },
    )
}

fn check_last(b: &mut Builder, prog: &[RamInstr], s: &RamState) -> RegSecretBit {
    let expect_pc = b.ld(prog.len() as u32);
    let pc_ok = b.eq(s.pc, expect_pc);
    let expect_r0 = b.ld(0);
    let r0_ok = b.eq(s.regs[0], expect_r0);
    b.and(pc_ok, r0_ok)
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

        let mut ok: RegSecretBit = b.ld(1);

        for (s1, s2) in trace.iter().zip(trace.iter().skip(1)) {
            let step_ok = check_step(&mut b, &prog, s1, s2);
            ok = b.and(ok, step_ok);
        }

        let last_ok = check_last(&mut b, &prog, trace.last().unwrap());
        ok = b.and(ok, last_ok);

        let ok_sr = b.sb_to_sr(ok);
        let ok_clear = b.reveal(ok_sr);
        b.print(ok_clear);
    }

    let instrs = b.finish();
    let mut f = BufWriter::new(File::create("out.bc")?);
    for i in instrs {
        scale_isa::functions::write_instruction(&mut f, i)?;
    }

    Ok(())
}
