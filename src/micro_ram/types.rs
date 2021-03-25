use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use serde::Deserialize;
use crate::eval::Evaluator;
use crate::gadget::bit_pack;
use crate::ir::circuit::{Circuit, Wire, Ty, TyKind, IntSize};
use crate::ir::typed::{
    self, Builder, TWire, TSecretHandle, Repr, Flatten, Lit, Secret, Mux, FromEval,
};
use crate::micro_ram::feature::{Feature, Version};


/// A TinyRAM instruction.  The program itself is not secret, but we most commonly load
/// instructions from secret indices, which results in a secret instruction.
#[derive(Clone, Copy, Debug, Default)]
pub struct RamInstr {
    pub opcode: u8,
    pub dest: u8,
    pub op1: u8,
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
            dest: dest as u8,
            op1: op1 as u8,
            op2: op2 as u64,
            imm,
        }
    }

    pub fn opcode(&self) -> Opcode {
        Opcode::from_raw(self.opcode).unwrap()
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

pub const REG_NONE: u8 = 254;
pub const REG_PC: u8 = 255;

#[derive(Clone, Copy)]
pub struct RamInstrRepr<'a> {
    pub opcode: TWire<'a, u8>,
    pub dest: TWire<'a, u8>,
    pub op1: TWire<'a, u8>,
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

impl<'a> Secret<'a> for RamInstr {
    fn secret(bld: &Builder<'a>) -> Self::Repr {
        RamInstrRepr {
            opcode: bld.with_label("opcode", || bld.secret_uninit()),
            dest: bld.with_label("dest", || bld.secret_uninit()),
            op1: bld.with_label("op1", || bld.secret_uninit()),
            op2: bld.with_label("op2", || bld.secret_uninit()),
            imm: bld.with_label("imm", || bld.secret_uninit()),
        }
    }

    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool) {
        Builder::set_secret_from_lit(&s.opcode, &val.opcode, force);
        Builder::set_secret_from_lit(&s.dest, &val.dest, force);
        Builder::set_secret_from_lit(&s.op1, &val.op1, force);
        Builder::set_secret_from_lit(&s.op2, &val.op2, force);
        Builder::set_secret_from_lit(&s.imm, &val.imm, force);
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

impl<'a> typed::Eq<'a, RamInstr> for RamInstr {
    type Output = bool;
    fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        let parts = [
            bld.eq(a.opcode, b.opcode),
            bld.eq(a.dest, b.dest),
            bld.eq(a.op1, b.op1),
            bld.eq(a.op2, b.op2),
            bld.eq(a.imm, b.imm),
        ];
        let mut acc = parts[0];
        for &part in &parts[1..] {
            acc = bld.and(acc, part);
        }
        acc.repr
    }
}



#[derive(Clone, Debug, Deserialize)]
pub struct RamState {
    pub pc: u64,
    pub regs: Vec<u64>,
    // All states parsed from the trace are assumed to be live.
    #[serde(default = "return_true")]
    pub live: bool,
    #[serde(default)]
    pub cycle: u32,
}

fn return_true() -> bool { true }

impl RamState {
    pub fn new(cycle: u32, pc: u32, regs: Vec<u32>, live: bool) -> RamState {
        RamState {
            cycle,
            pc: pc as u64,
            regs: regs.into_iter().map(|x| x as u64).collect(),
            live,
        }
    }

    pub fn default_with_regs(num_regs: usize) -> RamState {
        RamState {
            cycle: 0,
            pc: 0,
            regs: vec![0; num_regs],
            live: false,
        }
    }
}

#[derive(Clone)]
pub struct RamStateRepr<'a> {
    pub cycle: TWire<'a, u32>,
    pub pc: TWire<'a, u64>,
    pub regs: Vec<TWire<'a, u64>>,
    pub live: TWire<'a, bool>,
}

impl<'a> Repr<'a> for RamState {
    type Repr = RamStateRepr<'a>;
}

impl<'a> Lit<'a> for RamState {
    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        RamStateRepr {
            cycle: bld.lit(a.cycle),
            pc: bld.lit(a.pc),
            regs: bld.lit(a.regs).repr,
            live: bld.lit(a.live),
        }
    }
}

impl<'a> Secret<'a> for RamState {
    fn secret(_bld: &Builder<'a>) -> Self::Repr {
        panic!("can't construct RamState via Builder::secret - use RamState::secret instead");
    }

    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool) {
        Builder::set_secret_from_lit(&s.cycle, &val.cycle, force);
        Builder::set_secret_from_lit(&s.pc, &val.pc, force);
        assert_eq!(s.regs.len(), val.regs.len());
        for (s_reg, val_reg) in s.regs.iter().zip(val.regs.iter()) {
            Builder::set_secret_from_lit(s_reg, val_reg, force);
        }
        Builder::set_secret_from_lit(&s.live, &val.live, force);
    }
}

impl RamState {
    pub fn secret_with_value<'a>(bld: &Builder<'a>, a: Self) -> TWire<'a, RamState> {
        TWire::new(RamStateRepr {
            cycle: bld.with_label("cycle", || bld.secret_init(|| a.cycle)),
            pc: bld.with_label("pc", || bld.secret_init(|| a.pc)),
            regs: bld.with_label("regs", || {
                a.regs.iter().enumerate().map(|(i, &x)| {
                    bld.with_label(i, || bld.secret_init(|| x))
                }).collect()
            }),
            live: bld.with_label("live", || bld.secret_init(|| a.live)),
        })
    }

    pub fn secret_with_len<'a>(bld: &Builder<'a>, len: usize) -> TWire<'a, RamState> {
        TWire::new(RamStateRepr {
            cycle: bld.with_label("cycle", || bld.secret_uninit()),
            pc: bld.with_label("pc", || bld.secret_uninit()),
            regs: bld.with_label("regs", || (0 .. len).map(|i| {
                bld.with_label(i, || bld.secret_uninit())
            }).collect()),
            live: bld.with_label("live", || bld.secret_uninit()),
        })
    }

    pub fn secret<'a>(
        bld: &Builder<'a>,
        len: usize,
    ) -> (TWire<'a, RamState>, TSecretHandle<'a, RamState>) {
        let wire = Self::secret_with_len(bld, len);
        let default = bld.lit(RamState {
            cycle: 0,
            pc: 0,
            regs: vec![0; len],
            live: false,
        });
        (wire.clone(), TSecretHandle::new(wire, default))
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, RamState> for RamState
where
    C::Repr: Clone,
    u32: Mux<'a, C, u32, Output = u32>,
    <u32 as Repr<'a>>::Repr: Copy,
    u64: Mux<'a, C, u64, Output = u64>,
    <u64 as Repr<'a>>::Repr: Copy,
    bool: Mux<'a, C, bool, Output = bool>,
    <bool as Repr<'a>>::Repr: Copy,
{
    type Output = RamState;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        t: Self::Repr,
        e: Self::Repr,
    ) -> Self::Repr {
        let c: TWire<C> = TWire::new(c);
        assert_eq!(t.regs.len(), e.regs.len());
        RamStateRepr {
            cycle: bld.mux(c.clone(), t.cycle, e.cycle),
            pc: bld.mux(c.clone(), t.pc, e.pc),
            regs: t.regs.iter().zip(e.regs.iter())
                .map(|(&t_reg, &e_reg)| bld.mux(c.clone(), t_reg, e_reg))
                .collect(),
            live: bld.mux(c.clone(), t.live, e.live),
        }
    }
}

impl<'a> typed::Eq<'a, RamState> for RamState {
    type Output = bool;
    fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        assert_eq!(a.regs.len(), b.regs.len());
        let mut acc = bld.lit(true);
        acc = bld.and(acc, bld.eq(a.cycle, b.cycle));
        acc = bld.and(acc, bld.eq(a.pc, b.pc));
        for (&a_reg, &b_reg) in a.regs.iter().zip(b.regs.iter()) {
            acc = bld.and(acc, bld.eq(a_reg, b_reg));
        }
        acc = bld.and(acc, bld.eq(a.live, b.live));
        acc.repr
    }
}



macro_rules! mk_named_enum {
    (
        $(#[$attr:meta])*
        $vis:vis enum $Name:ident {
            $(
                $(#[$var_attr:meta])*
                $Variant:ident = $value:expr,
            )*
        }
    ) => {
        $(#[$attr])*
        #[repr(u8)]
        $vis enum $Name {
            $(
                $(#[$var_attr])*
                $Variant = $value,
            )*
        }

        impl $Name {
            const COUNT: usize = 0 $( + {
                #[allow(bad_style)] let $Variant = 1;
                $Variant
            } )*;

            pub fn from_raw(x: u8) -> Option<$Name> {
                Some(match x {
                    $($value => $Name::$Variant,)*
                    _ => return None,
                })
            }

            pub fn iter() -> impl Iterator<Item = $Name> {
                const ALL: [$Name; $Name::COUNT] = [ $( $Name::$Variant, )* ];
                ALL.iter().cloned()
            }

            pub fn from_str(s: &str) -> Option<$Name> {
                $( if s.eq_ignore_ascii_case(stringify!($Variant)) {
                    return Some($Name::$Variant);
                } )*
                None
            }
        }


        impl<'a> Repr<'a> for $Name {
            type Repr = TWire<'a, u8>;
        }

        impl<'a> Flatten<'a> for $Name {
            fn wire_type(c: &Circuit<'a>) -> Ty<'a> { c.ty(TyKind::U8) }
            fn to_wire(_bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr.repr }
            fn from_wire(_bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                assert!(*w.ty == TyKind::U8);
                TWire::new(TWire::new(w))
            }
        }

        impl<'a> Lit<'a> for $Name {
            fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
                bld.lit(a as u8)
            }
        }

        impl<'a> Secret<'a> for $Name {
            fn secret(bld: &Builder<'a>) -> Self::Repr {
                bld.secret_uninit()
            }

            fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool) {
                Builder::set_secret_from_lit(s, val, force);
            }
        }

        impl<'a> typed::Eq<'a, $Name> for $Name {
            type Output = bool;
            fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
                bld.eq(a, b).repr
            }
        }

        impl<'a> typed::Ne<'a, $Name> for $Name {
            type Output = bool;
            fn ne(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
                bld.ne(a, b).repr
            }
        }

        impl<'a> FromEval<'a> for $Name {
            fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Self::Repr) -> Option<Self> {
                let raw = u8::from_eval(ev, a.repr)?;
                let result = Self::from_raw(raw);
                if result.is_none() {
                    eprintln!(
                        "warning: evaluation of {} produced out-of-range value {}",
                        stringify!($Name), raw,
                    );
                }
                result
            }
        }
    };
}

mk_named_enum! {
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub enum Opcode {
        And = 0,
        Or = 1,
        Xor = 2,
        Not = 3,
        Add = 4,
        Sub = 5,
        Mull = 6,
        Umulh = 7,
        Smulh = 8,
        Udiv = 9,
        Umod = 10,
        Shl = 11,
        Shr = 12,

        Cmpe = 13,
        Cmpa = 14,
        Cmpae = 15,
        Cmpg = 16,
        Cmpge = 17,

        Mov = 18,
        Cmov = 19,

        Jmp = 20,
        Cjmp = 21,
        Cnjmp = 22,

        Store1 = 23,
        Store2 = 24,
        Store4 = 25,
        Store8 = 26,
        Load1 = 27,
        Load2 = 28,
        Load4 = 29,
        Load8 = 30,
        Poison8 = 31,

        Read = 32,
        Answer = 33,

        Advise = 34,

        /// Fake instruction that does nothing and doesn't advace the PC.  `Advice::Stutter` causes
        /// this instruction to be used in place of the one that was fetched.
        Stutter = 255,
    }
}

impl Opcode {
    pub fn is_mem(&self) -> bool {
        use Opcode::*;
        match *self {
            Store1 | Store2 | Store4 | Store8 |
            Load1 | Load2 | Load4 | Load8 |
            Poison8 => true,
            _ => false,
        }
    }
}


pub const MEM_PORT_UNUSED_CYCLE: u32 = !0 - 1;
pub const MEM_PORT_PRELOAD_CYCLE: u32 = !0;

#[derive(Clone, Copy, Debug, Default)]
pub struct MemPort {
    /// The cycle on which this operation occurs.
    pub cycle: u32,
    /// The address accessed in this operation.  Must be well aligned; that is, `addr` must be a
    /// multiple of the `width.bytes()`.
    pub addr: u64,
    /// The value of the aligned word that contains `addr` after the execution of this operation.
    /// For example, if `addr` is `0x13`, then `value` is the value of the word starting at `0x10`.
    pub value: u64,
    pub op: MemOpKind,
    /// The width of this memory access.  For `Write` and `Poison` operations, only the
    /// `width.bytes()` bytes starting at `addr` may be modified; if `width < MemOpWidth::WORD`,
    /// then all other bytes of `value` must be copied from the previous value of the modified
    /// word.  For `Read` operations, `width` is only used to check the alignment of `addr`, as
    /// `value` must exactly match the previous value of the accessed word.
    pub width: MemOpWidth,
}


mk_named_enum! {
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub enum MemOpKind {
        Read = 0,
        Write = 1,
        Poison = 2,
    }
}

impl Default for MemOpKind {
    fn default() -> MemOpKind { MemOpKind::Read }
}

impl<'a, C: Repr<'a>> Mux<'a, C, MemOpKind> for MemOpKind
where
    C::Repr: Clone,
    u8: Mux<'a, C, u8, Output = u8>,
{
    type Output = MemOpKind;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        t: TWire<'a, u8>,
        e: TWire<'a, u8>,
    ) -> TWire<'a, u8> {
        bld.mux(TWire::new(c), t, e)
    }
}


mk_named_enum! {
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub enum MemOpWidth {
        W1 = 0,
        W2 = 1,
        W4 = 2,
        W8 = 3,
    }
}

impl MemOpWidth {
    pub const WORD: MemOpWidth = MemOpWidth::W8;

    pub const fn bytes(self) -> usize {
        1_usize << (self as u8)
    }

    pub const fn bits(self) -> usize {
        self.bytes() * 8
    }

    pub const fn log_bytes(self) -> usize {
        self as u8 as usize
    }

    pub const fn load_opcode(self) -> Opcode {
        match self {
            MemOpWidth::W1 => Opcode::Load1,
            MemOpWidth::W2 => Opcode::Load2,
            MemOpWidth::W4 => Opcode::Load4,
            MemOpWidth::W8 => Opcode::Load8,
        }
    }

    pub const fn store_opcode(self) -> Opcode {
        match self {
            MemOpWidth::W1 => Opcode::Store1,
            MemOpWidth::W2 => Opcode::Store2,
            MemOpWidth::W4 => Opcode::Store4,
            MemOpWidth::W8 => Opcode::Store8,
        }
    }
}

pub const WORD_BYTES: usize = MemOpWidth::WORD.bytes();
pub const WORD_BITS: usize = MemOpWidth::WORD.bits();
pub const WORD_LOG_BYTES: usize = MemOpWidth::WORD.log_bytes();

impl Default for MemOpWidth {
    fn default() -> MemOpWidth { MemOpWidth::WORD }
}

impl<'a, C: Repr<'a>> Mux<'a, C, MemOpWidth> for MemOpWidth
where
    C::Repr: Clone,
    u8: Mux<'a, C, u8, Output = u8>,
{
    type Output = MemOpWidth;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        t: TWire<'a, u8>,
        e: TWire<'a, u8>,
    ) -> TWire<'a, u8> {
        bld.mux(TWire::new(c), t, e)
    }
}


#[derive(Clone, Copy)]
pub struct MemPortRepr<'a> {
    pub cycle: TWire<'a, u32>,
    pub addr: TWire<'a, u64>,
    pub value: TWire<'a, u64>,
    pub op: TWire<'a, MemOpKind>,
    pub width: TWire<'a, MemOpWidth>,
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
            op: bld.lit(a.op),
            width: bld.lit(a.width),
        }
    }
}

impl<'a> Secret<'a> for MemPort {
    fn secret(bld: &Builder<'a>) -> Self::Repr {
        MemPortRepr {
            cycle: bld.with_label("cycle", || bld.secret_uninit()),
            addr: bld.with_label("addr", || bld.secret_uninit()),
            value: bld.with_label("value", || bld.secret_uninit()),
            op: bld.with_label("op", || bld.secret_uninit()),
            width: bld.with_label("width", || bld.secret_uninit()),
        }
    }

    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool) {
        Builder::set_secret_from_lit(&s.cycle, &val.cycle, force);
        Builder::set_secret_from_lit(&s.addr, &val.addr, force);
        Builder::set_secret_from_lit(&s.value, &val.value, force);
        Builder::set_secret_from_lit(&s.op, &val.op, force);
        Builder::set_secret_from_lit(&s.width, &val.width, force);
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, MemPort> for MemPort
where
    C::Repr: Clone,
    u32: Mux<'a, C, u32, Output = u32>,
    u64: Mux<'a, C, u64, Output = u64>,
    MemOpKind: Mux<'a, C, MemOpKind, Output = MemOpKind>,
    MemOpWidth: Mux<'a, C, MemOpWidth, Output = MemOpWidth>,
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
            op: bld.mux(c.clone(), t.op, e.op),
            width: bld.mux(c.clone(), t.width, e.width),
        }
    }
}


pub struct ByteOffset(u8);

impl ByteOffset {
    pub fn new(x: u8) -> ByteOffset {
        assert!((x as usize) < MemOpWidth::WORD.bytes());
        ByteOffset(x)
    }

    pub fn raw(self) -> u8 {
        self.0
    }
}

impl<'a> Repr<'a> for ByteOffset {
    type Repr = Wire<'a>;
}

impl<'a> Flatten<'a> for ByteOffset {
    fn wire_type(c: &Circuit<'a>) -> Ty<'a> {
        c.ty(TyKind::Uint(IntSize(MemOpWidth::WORD.log_bytes() as u16)))
    }

    fn to_wire(_bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        w.repr
    }

    fn from_wire(_bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(w)
    }
}

impl<'a> Lit<'a> for ByteOffset {
    fn lit(bld: &Builder<'a>, x: Self) -> Wire<'a> {
        let c = bld.circuit();
        c.lit(Self::wire_type(c), x.raw() as u64)
    }
}

impl<'a> Mux<'a, bool, ByteOffset> for ByteOffset {
    type Output = ByteOffset;
    fn mux(bld: &Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        bld.circuit().mux(c, t, e)
    }
}


impl<'a> typed::Eq<'a, ByteOffset> for ByteOffset {
    type Output = bool;
    fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a, b)
    }
}

pub struct WordAddr;

impl<'a> Repr<'a> for WordAddr {
    type Repr = Wire<'a>;
}

impl<'a> Flatten<'a> for WordAddr {
    fn wire_type(c: &Circuit<'a>) -> Ty<'a> {
        c.ty(TyKind::Uint(IntSize(
            MemOpWidth::WORD.bits() as u16 - MemOpWidth::WORD.log_bytes() as u16)))
    }

    fn to_wire(_bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        w.repr
    }

    fn from_wire(_bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(w)
    }
}

impl<'a> typed::Eq<'a, WordAddr> for WordAddr {
    type Output = bool;
    fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a, b)
    }
}


pub struct PackedMemPort;

#[derive(Clone, Copy)]
pub struct PackedMemPortRepr<'a> {
    key: Wire<'a>,
    data: Wire<'a>,
}

impl PackedMemPort {
    pub fn from_unpacked<'a>(
        bld: &Builder<'a>,
        mp: TWire<'a, MemPort>,
    ) -> TWire<'a, PackedMemPort> {
        // Add 1 to the cycle numbers so that MEM_PORT_UNUSED_CYCLE (-1) comes before all real
        // cycles.
        let cycle_adj = bld.add(mp.cycle, bld.lit(1));
        // Split the address into word (upper 61 bits) and offset (lower 3 bits) parts.
        let (offset, waddr) = *bit_pack::split_bits::<(ByteOffset, WordAddr)>(bld, mp.addr.repr);
        // ConcatBits is little-endian.  To sort by `addr` first and then by `cycle`, we have to
        // put `addr` last in the list.
        let key = bit_pack::concat_bits(bld, TWire::<(_, _)>::new((cycle_adj, waddr)));
        let data = bit_pack::concat_bits(bld, TWire::<(_, _, _, _)>::new((
            mp.value, mp.op, mp.width, offset)));
        TWire::new(PackedMemPortRepr { key, data })
    }
}

impl<'a> PackedMemPortRepr<'a> {
    pub fn unpack(&self, bld: &Builder<'a>) -> TWire<'a, MemPort> {
        let (cycle_adj, waddr) = *bit_pack::split_bits::<(u32, WordAddr)>(bld, self.key);
        let cycle = bld.sub(cycle_adj, bld.lit(1));
        let (value, op, width, offset) =
            *bit_pack::split_bits::<(_, _, _, ByteOffset)>(bld, self.data);
        let addr = TWire::new(bit_pack::concat_bits(bld, TWire::<(_, _)>::new((offset, waddr))));
        TWire::new(MemPortRepr { cycle, addr, value, op, width })
    }
}

impl<'a> Repr<'a> for PackedMemPort {
    type Repr = PackedMemPortRepr<'a>;
}

impl<'a> Mux<'a, bool, PackedMemPort> for PackedMemPort {
    type Output = PackedMemPort;

    fn mux(
        bld: &Builder<'a>,
        c: Wire<'a>,
        t: Self::Repr,
        e: Self::Repr,
    ) -> Self::Repr {
        PackedMemPortRepr {
            key: bld.circuit().mux(c, t.key, e.key),
            data: bld.circuit().mux(c, t.data, e.data),
        }
    }
}

impl<'a> typed::Eq<'a, PackedMemPort> for PackedMemPort {
    type Output = bool;
    fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a.key, b.key)
    }
}

impl<'a> typed::Lt<'a, PackedMemPort> for PackedMemPort {
    type Output = bool;
    fn lt(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().lt(a.key, b.key)
    }
}

impl<'a> typed::Le<'a, PackedMemPort> for PackedMemPort {
    type Output = bool;
    fn le(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().le(a.key, b.key)
    }
}


/// A simplified version of `MemPort` used for instruction fetch.  Since all accesses after
/// initialization are reads, we don't need to track the cycle number - we sort by `(addr, !write)`
/// instead of `(addr, cycle)`.
#[derive(Clone, Copy, Default)]
pub struct FetchPort {
    pub addr: u64,
    pub instr: RamInstr,
    pub write: bool,
}

#[derive(Clone, Copy)]
pub struct FetchPortRepr<'a> {
    pub addr: TWire<'a, u64>,
    pub instr: TWire<'a, RamInstr>,
    pub write: TWire<'a, bool>,
}

impl<'a> Repr<'a> for FetchPort {
    type Repr = FetchPortRepr<'a>;
}

impl<'a> Lit<'a> for FetchPort {
    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        FetchPortRepr {
            addr: bld.lit(a.addr),
            instr: bld.lit(a.instr),
            write: bld.lit(a.write),
        }
    }
}

impl<'a> Secret<'a> for FetchPort {
    fn secret(bld: &Builder<'a>) -> Self::Repr {
        FetchPortRepr {
            addr: bld.with_label("addr", || bld.secret_uninit()),
            instr: bld.with_label("instr", || bld.secret_uninit()),
            write: bld.with_label("write", || bld.secret_uninit()),
        }
    }

    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool) {
        Builder::set_secret_from_lit(&s.addr, &val.addr, force);
        Builder::set_secret_from_lit(&s.instr, &val.instr, force);
        Builder::set_secret_from_lit(&s.write, &val.write, force);
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, FetchPort> for FetchPort
where
    C::Repr: Clone,
    u64: Mux<'a, C, u64, Output = u64>,
    RamInstr: Mux<'a, C, RamInstr, Output = RamInstr>,
    bool: Mux<'a, C, bool, Output = bool>,
{
    type Output = FetchPort;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        t: FetchPortRepr<'a>,
        e: FetchPortRepr<'a>,
    ) -> FetchPortRepr<'a> {
        let c: TWire<C> = TWire::new(c);
        FetchPortRepr {
            addr: bld.mux(c.clone(), t.addr, e.addr),
            instr: bld.mux(c.clone(), t.instr, e.instr),
            write: bld.mux(c.clone(), t.write, e.write),
        }
    }
}

pub struct PackedFetchPort;

#[derive(Clone, Copy)]
pub struct PackedFetchPortRepr<'a> {
    key: Wire<'a>,
    data: Wire<'a>,
}

impl PackedFetchPort {
    pub fn from_unpacked<'a>(
        bld: &Builder<'a>,
        fp: TWire<'a, FetchPort>,
    ) -> TWire<'a, PackedFetchPort> {
        // ConcatBits is little-endian.  To sort by `addr` first and then by `write`, we have to
        // put `addr` last in the list.
        let key = bit_pack::concat_bits(bld, TWire::<(_, _)>::new((bld.not(fp.write), fp.addr)));
        let data = bit_pack::concat_bits(bld, TWire::<(_, _, _, _, _)>::new((
            fp.instr.opcode,
            fp.instr.dest,
            fp.instr.op1,
            fp.instr.op2,
            fp.instr.imm,
        )));
        TWire::new(PackedFetchPortRepr { key, data })
    }
}

impl<'a> PackedFetchPortRepr<'a> {
    pub fn unpack(&self, bld: &Builder<'a>) -> TWire<'a, FetchPort> {
        let (not_write, addr) = *bit_pack::split_bits::<(_, _)>(bld, self.key);
        let (opcode, dest, op1, op2, imm) =
            *bit_pack::split_bits::<(_, _, _, _, _)>(bld, self.data);
        TWire::new(FetchPortRepr {
            addr,
            instr: TWire::new(RamInstrRepr { opcode, dest, op1, op2, imm }),
            write: bld.not::<bool>(not_write),
        })
    }
}

impl<'a> Repr<'a> for PackedFetchPort {
    type Repr = PackedFetchPortRepr<'a>;
}

impl<'a> Mux<'a, bool, PackedFetchPort> for PackedFetchPort {
    type Output = PackedFetchPort;

    fn mux(
        bld: &Builder<'a>,
        c: Wire<'a>,
        t: Self::Repr,
        e: Self::Repr,
    ) -> Self::Repr {
        PackedFetchPortRepr {
            key: bld.circuit().mux(c, t.key, e.key),
            data: bld.circuit().mux(c, t.data, e.data),
        }
    }
}

impl<'a> typed::Eq<'a, PackedFetchPort> for PackedFetchPort {
    type Output = bool;
    fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a.key, b.key)
    }
}

impl<'a> typed::Lt<'a, PackedFetchPort> for PackedFetchPort {
    type Output = bool;
    fn lt(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().lt(a.key, b.key)
    }
}

impl<'a> typed::Le<'a, PackedFetchPort> for PackedFetchPort {
    type Output = bool;
    fn le(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().le(a.key, b.key)
    }
}




#[derive(Clone, Debug)]
pub struct Execution {
    pub version: Version,
    /// The set of all enabled features.  This is built by combining `declared_features` with the
    /// baseline features implied by `version`.
    pub features: HashSet<Feature>,
    /// The set of features explicitly declared in the version header.
    pub declared_features: HashSet<Feature>,

    pub program: Vec<RamInstr>,
    pub init_mem: Vec<MemSegment>,
    pub params: Params,
    pub segments: Vec<Segment>,
    pub trace: Vec<TraceChunk>,
    pub advice: HashMap<u64, Vec<Advice>>,
}

impl Execution {
    pub fn has_feature(&self, feature: Feature) -> bool {
        self.features.contains(&feature)
    }

    pub fn validate(self) -> Result<Self, String> {
        let params = &self.params;
        if !self.features.contains(&Feature::PublicPc) {
            if self.segments.len() != 0 {
                return Err(format!(
                    "expected no segment definitions in non-public-pc trace, but got {}",
                    self.segments.len(),
                ));
            }

            if self.trace.len() != 1 {
                return Err(format!(
                    "expected exactly one trace chunk in non-public-pc trace, but got {}",
                    self.trace.len(),
                ));
            }

            if self.params.trace_len.is_none() {
                return Err(format!("non-public-pc trace must have `params.trace_len` set"));
            }

            let expect_trace_len = self.params.trace_len.unwrap();
            if self.trace[0].states.len() != expect_trace_len {
                return Err(format!(
                    "wrong number of states in trace: expected {}, but got {}",
                    expect_trace_len, self.trace[0].states.len(),
                ));
            }
        }

        for (i, seg) in self.segments.iter().enumerate() {
            for &idx in &seg.successors {
                if idx >= self.segments.len() {
                    return Err(format!(
                        "`segments[{}]` has out-of-range successor {} (len = {})",
                        i, idx, self.segments.len(),
                    ));
                }
            }
        }

        for (i, chunk) in self.trace.iter().enumerate() {
            if !self.features.contains(&Feature::PublicPc) {
                if chunk.segment != 0 {
                    return Err(format!(
                        "`trace[{}]` references segment {} in non-public-pc mode",
                        i, chunk.segment,
                    ));
                }
            } else {
                if chunk.segment >= self.segments.len() {
                    return Err(format!(
                        "`trace[{}]` references undefined segment {} (len = {})",
                        i, chunk.segment, self.segments.len(),
                    ));
                }

                let expect_len = self.segments[chunk.segment].len;
                if chunk.states.len() != expect_len {
                    return Err(format!(
                        "`trace[{}]` for segment {} should have {} states, but has {}",
                        i, chunk.segment, expect_len, chunk.states.len(),
                    ));
                }
            }

            for (j, state) in chunk.states.iter().enumerate() {
                if state.regs.len() != params.num_regs {
                    return Err(format!(
                        "`trace[{}][{}]` should have {} register values (`num_regs`), not {}",
                        i, j, params.num_regs, state.regs.len(),
                    ));
                }
            }
        }

        let trace_len = self.trace.iter().map(|c| c.states.len()).sum();
        for &i in self.advice.keys() {
            let i = usize::try_from(i)
                .map_err(|e| format!("advice key {} out of range: {}", i, e))?;
            if i >= trace_len {
                return Err(format!(
                    "`advice` key out of range: the index is {} but `trace` has only {} states",
                    i, trace_len,
                ));
            }
        }

        Ok(self)
    }
}

#[derive(Clone, Debug, Deserialize)]
pub struct MemSegment {
    pub start: u64,
    pub len: u64,
    pub read_only: bool,
    pub secret: bool,
    #[serde(default)]
    pub data: Vec<u64>,
}

#[derive(Clone, Debug, Default, Deserialize)]
pub struct Params {
    pub num_regs: usize,
    #[serde(default)]
    pub trace_len: Option<usize>,
    #[serde(alias = "sparcity", default)]
    pub sparsity: Sparsity,
}

#[derive(Clone, Debug, Deserialize)]
pub struct Sparsity {
    #[serde(alias = "KmemOp", default = "one")]
    pub mem_op: usize,
}

fn one() -> usize {
    1
}

impl Default for Sparsity {
    fn default() -> Sparsity {
        Sparsity {
            mem_op: 1,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Segment {
    pub constraints: Vec<SegmentConstraint>,
    pub len: usize,
    pub successors: Vec<usize>,
    pub enter_from_network: bool,
    pub exit_to_network: bool,
}

impl Segment {
    pub fn init_pc(&self) -> Option<u64> {
        for c in &self.constraints {
            match *c {
                SegmentConstraint::Pc(pc) => return Some(pc),
            }
        }
        None
    }
}

#[derive(Clone, Debug)]
pub enum SegmentConstraint {
    Pc(u64),
}

#[derive(Clone, Debug)]
pub enum Advice {
    MemOp {
        addr: u64,
        value: u64,
        op: MemOpKind,
        width: MemOpWidth,
    },
    Stutter,
    Advise { advise: u64 },
}

#[derive(Clone, Debug)]
pub struct TraceChunk {
    pub segment: usize,
    pub states: Vec<RamState>,
    /// Debug overrides.  Used to construct invalid traces for testing purposes.
    pub debug: Option<TraceChunkDebug>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct TraceChunkDebug {
    /// If set, force the cycle counter to this value before running the chunk.
    #[serde(default)]
    pub cycle: Option<u32>,
    /// If set, force the previous state to this value before running the chunk.
    #[serde(default)]
    pub prev_state: Option<RamState>,
    /// If set, force the previous-segment counter to `None` before running the chunk.
    #[serde(default)]
    pub clear_prev_segment: bool,
    /// If set, force the previous-segment counter to this value before running the chunk.
    #[serde(default)]
    pub prev_segment: Option<usize>,
}
