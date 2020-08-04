use crate::ir::typed::{Builder, TWire, Repr, Lit, Secret, Mux};


/// A TinyRAM instruction.  The program itself is not secret, but we most commonly load
/// instructions from secret indices, which results in a secret instruction.
#[derive(Clone, Copy)]
pub struct RamInstr {
    pub opcode: u8,
    pub dest: u64,
    pub op1: u64,
    pub op2: u64,
    /// Some opcodes have an operand that can be either a register name or an immediate value.  If
    /// `imm` is set, it's interpreted as an immediate; otherwise, it's a register.
    pub imm: bool,
}

impl RamInstr {
    pub fn new(
        opcode: Opcode,
        dest: u32,
        op1: u32,
        op2: u32,
        imm: bool,
    ) -> RamInstr {
        RamInstr {
            opcode: opcode as u8,
            dest: dest as u64,
            op1: op1 as u64,
            op2: op2 as u64,
            imm,
        }
    }

    pub fn mov(rd: u32, r1: u32) -> RamInstr {
        RamInstr::new(Opcode::Mov, rd, r1, 0, false)
    }

    pub fn mov_imm(rd: u32, imm: u32) -> RamInstr {
        RamInstr::new(Opcode::Mov, rd, imm, 0, true)
    }

    pub fn add(rd: u32, r1: u32, r2: u32) -> RamInstr {
        RamInstr::new(Opcode::Add, rd, r1, r2, false)
    }

    pub fn add_imm(rd: u32, r1: u32, imm: u32) -> RamInstr {
        RamInstr::new(Opcode::Add, rd, r1, imm, true)
    }

    pub fn sub(rd: u32, r1: u32, r2: u32) -> RamInstr {
        RamInstr::new(Opcode::Sub, rd, r1, r2, false)
    }

    pub fn sub_imm(rd: u32, r1: u32, imm: u32) -> RamInstr {
        RamInstr::new(Opcode::Sub, rd, r1, imm, true)
    }

    pub fn mull(rd: u32, r1: u32, r2: u32) -> RamInstr {
        RamInstr::new(Opcode::Mull, rd, r1, r2, false)
    }

    pub fn mull_imm(rd: u32, r1: u32, imm: u32) -> RamInstr {
        RamInstr::new(Opcode::Mull, rd, r1, imm, true)
    }
}

pub const REG_NONE: u64 = 1000;
pub const REG_PC: u64 = 1001;

#[derive(Clone, Copy)]
pub struct RamInstrRepr<'a> {
    pub opcode: TWire<'a, u8>,
    pub dest: TWire<'a, u64>,
    pub op1: TWire<'a, u64>,
    pub op2: TWire<'a, u64>,
    pub imm: TWire<'a, bool>,
}

impl<'a> Repr<'a> for RamInstr {
    type Repr = RamInstrRepr<'a>;
}

impl<'a> Lit<'a> for RamInstr {
    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        RamInstrRepr {
            opcode: bld.lit(a.opcode),
            dest: bld.lit(a.dest),
            op1: bld.lit(a.op1),
            op2: bld.lit(a.op2),
            imm: bld.lit(a.imm),
        }
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, RamInstr> for RamInstr
where
    C::Repr: Clone,
    u8: Mux<'a, C, u8, Output = u8>,
    u64: Mux<'a, C, u64, Output = u64>,
    bool: Mux<'a, C, bool, Output = bool>,
{
    type Output = RamInstr;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        t: RamInstrRepr<'a>,
        e: RamInstrRepr<'a>,
    ) -> RamInstrRepr<'a> {
        let c: TWire<C> = TWire::new(c);
        RamInstrRepr {
            opcode: bld.mux(c.clone(), t.opcode, e.opcode),
            dest: bld.mux(c.clone(), t.dest, e.dest),
            op1: bld.mux(c.clone(), t.op1, e.op1),
            op2: bld.mux(c.clone(), t.op2, e.op2),
            imm: bld.mux(c.clone(), t.imm, e.imm),
        }
    }
}


pub const RAM_REGS: usize = 16;

pub struct RamState {
    pub pc: u64,
    pub regs: [u64; RAM_REGS],
    pub flag: bool,
}

impl RamState {
    pub fn new(pc: u32, regs: [u32; RAM_REGS], flag: bool) -> RamState {
        let mut state_regs = [0; RAM_REGS];
        for i in 0 .. RAM_REGS {
            state_regs[i] = regs[i] as u64;
        }
        RamState {
            pc: pc as u64,
            regs: state_regs,
            flag,
        }
    }
}

#[derive(Clone, Copy)]
pub struct RamStateRepr<'a> {
    pub pc: TWire<'a, u64>,
    pub regs: [TWire<'a, u64>; RAM_REGS],
    pub flag: TWire<'a, bool>,
}

impl<'a> Repr<'a> for RamState {
    type Repr = RamStateRepr<'a>;
}

impl<'a> Lit<'a> for RamState {
    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        RamStateRepr {
            pc: bld.lit(a.pc),
            regs: *bld.lit(a.regs),
            flag: bld.lit(a.flag),
        }
    }
}

impl<'a> Secret<'a> for RamState {
    fn secret(bld: &Builder<'a>, a: Option<Self>) -> Self::Repr {
        if let Some(a) = a {
            RamStateRepr {
                pc: bld.secret(Some(a.pc)),
                regs: *bld.secret(Some(a.regs)),
                flag: bld.secret(Some(a.flag)),
            }
        } else {
            RamStateRepr {
                pc: bld.secret(None),
                regs: *bld.secret::<[u64; RAM_REGS]>(None),
                flag: bld.secret(None),
            }
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
                #![allow(unused)]   // Final write to `y` is never read
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
    And,
    Or,
    Xor,
    Not,
    Add,
    Sub,
    Mull,
    Umulh,
    Smulh,
    Udiv,
    Umod,
    Shl,
    Shr,

    Cmpe,
    Cmpa,
    Cmpae,
    Cmpg,
    Cmpge,

    Mov,
    Cmov,

    Jmp,
    Cjmp,
    Cnjmp,

    Store,
    Load,
}


#[derive(Clone, Copy, Default)]
pub struct MemPort {
    pub cycle: u32,
    pub addr: u64,
    pub value: u64,
    pub write: bool,
}

#[derive(Clone, Copy)]
pub struct MemPortRepr<'a> {
    pub cycle: TWire<'a, u32>,
    pub addr: TWire<'a, u64>,
    pub value: TWire<'a, u64>,
    pub write: TWire<'a, bool>,
}

impl<'a> Repr<'a> for MemPort {
    type Repr = MemPortRepr<'a>;
}

impl<'a> Lit<'a> for MemPort {
    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        MemPortRepr {
            cycle: bld.lit(a.cycle),
            addr: bld.lit(a.addr),
            value: bld.lit(a.value),
            write: bld.lit(a.write),
        }
    }
}

impl<'a> Secret<'a> for MemPort {
    fn secret(bld: &Builder<'a>, a: Option<Self>) -> Self::Repr {
        if let Some(a) = a {
            MemPortRepr {
                cycle: bld.secret(Some(a.cycle)),
                addr: bld.secret(Some(a.addr)),
                value: bld.secret(Some(a.value)),
                write: bld.secret(Some(a.write)),
            }
        } else {
            MemPortRepr {
                cycle: bld.secret(None),
                addr: bld.secret(None),
                value: bld.secret(None),
                write: bld.secret(None),
            }
        }
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, MemPort> for MemPort
where
    C::Repr: Clone,
    u32: Mux<'a, C, u32, Output = u32>,
    u64: Mux<'a, C, u64, Output = u64>,
    bool: Mux<'a, C, bool, Output = bool>,
{
    type Output = MemPort;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        t: MemPortRepr<'a>,
        e: MemPortRepr<'a>,
    ) -> MemPortRepr<'a> {
        let c: TWire<C> = TWire::new(c);
        MemPortRepr {
            cycle: bld.mux(c.clone(), t.cycle, e.cycle),
            addr: bld.mux(c.clone(), t.addr, e.addr),
            value: bld.mux(c.clone(), t.value, e.value),
            write: bld.mux(c.clone(), t.write, e.write),
        }
    }
}
