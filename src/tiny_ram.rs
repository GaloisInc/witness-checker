use scale_isa::types::{RegSecretRegint, RegSecretBit};
use crate::builder::{Builder, Mux};


/// A TinyRAM instruction.  The program itself is not secret, but we most commonly load
/// instructions from secret indices, which results in a secret instruction.
#[derive(Clone, Copy)]
pub struct RamInstr {
    pub opcode: RegSecretRegint,
    pub dest: RegSecretRegint,
    pub op1: RegSecretRegint,
    pub op2: RegSecretRegint,
    /// Some opcodes have an operand that can be either a register name or an immediate value.  If
    /// `imm` is set, it's interpreted as an immediate; otherwise, it's a register.
    pub imm: RegSecretBit,
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

pub const RAM_REGS: usize = 3;

pub struct RamState {
    pub pc: RegSecretRegint,
    pub regs: [RegSecretRegint; RAM_REGS],
    pub flag: RegSecretBit,
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
        pub enum Opcode {
            $($Variant,)*
        }

        impl Opcode {
            pub fn from_raw(x: u8) -> Opcode {
                let mut y = x;
                $(
                    if y == 0 { return Opcode::$Variant; }
                    y -= 1;
                )*
                panic!("bad value {} for Opcode", x)
            }

            pub fn count() -> usize {
                0 $(+ { drop(Opcode::$Variant); 1})*
            }

            pub fn iter() -> impl Iterator<Item = Opcode> {
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
