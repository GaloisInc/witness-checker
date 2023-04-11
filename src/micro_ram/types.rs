use std::cmp::{self, Ordering};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt;
use serde::{de, Deserialize};
use zk_circuit_builder::eval::Evaluator;
use zk_circuit_builder::gadget::bit_pack;
use zk_circuit_builder::ir::circuit::{
    CircuitBase, CircuitTrait, CircuitExt, Wire, Ty, TyKind, IntSize, Bits,
};
use zk_circuit_builder::ir::typed::{
    self, Builder, BuilderExt, TWire, Repr, Flatten, Lit, Mux, FromEval, LazySecret, SecretDep,
    FromWireList, ToWireList,
};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::primitive_binary_impl;
use zk_circuit_builder::routing::sort::Sortable;
use crate::micro_ram::feature::{Feature, Version};
use crate::micro_ram::types::typed::{Cast, Eq, Le, Lt, Ge, Gt, Ne};
use crate::mode::if_mode::{IfMode, AnyTainted, check_mode, panic_default};


/// A TinyRAM instruction.  The program itself is not secret, but we most commonly load
/// instructions from secret indices, which results in a secret instruction.
#[derive(Clone, Copy, Debug, Default, Migrate, FromWireList)]
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

#[derive(Clone, Copy, Migrate)]
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
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        RamInstrRepr {
            opcode: bld.lit(a.opcode),
            dest: bld.lit(a.dest),
            op1: bld.lit(a.op1),
            op2: bld.lit(a.op2),
            imm: bld.lit(a.imm),
        }
    }
}

impl<'a> LazySecret<'a> for RamInstr {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u8::expected_word_len(sizes) +
        u8::expected_word_len(sizes) +
        u8::expected_word_len(sizes) +
        u64::expected_word_len(sizes) +
        bool::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        let RamInstr { opcode, dest, op1, op2, imm } = *self;
        opcode.word_len() +
        dest.word_len() +
        op1.word_len() +
        op2.word_len() +
        imm.word_len()
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        let RamInstr { opcode, dest, op1, op2, imm } = *self;
        opcode.push_words(out);
        dest.push_words(out);
        op1.push_words(out);
        op2.push_words(out);
        imm.push_words(out);
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
        bld: &impl Builder<'a>,
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
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
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

impl<'a> ToWireList<'a> for RamInstr {
    fn num_wires(x: &Self::Repr) -> usize {
        let RamInstrRepr { ref opcode, ref dest, ref op1, ref op2, ref imm } = *x;
        u8::num_wires(opcode) +
        u8::num_wires(dest) +
        u8::num_wires(op1) +
        u64::num_wires(op2) +
        bool::num_wires(imm)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        let RamInstrRepr { ref opcode, ref dest, ref op1, ref op2, ref imm } = *x;
        u8::for_each_wire(opcode, |w| f(w));
        u8::for_each_wire(dest, |w| f(w));
        u8::for_each_wire(op1, |w| f(w));
        u64::for_each_wire(op2, |w| f(w));
        bool::for_each_wire(imm, |w| f(w));
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        let RamInstrRepr { ref opcode, ref dest, ref op1, ref op2, ref imm } = *x;
        u8::num_sizes(opcode) +
        u8::num_sizes(dest) +
        u8::num_sizes(op1) +
        u64::num_sizes(op2) +
        bool::num_sizes(imm)
    }
    fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
        let RamInstrRepr { ref opcode, ref dest, ref op1, ref op2, ref imm } = *x;
        u8::for_each_size(opcode, |s| f(s));
        u8::for_each_size(dest, |s| f(s));
        u8::for_each_size(op1, |s| f(s));
        u64::for_each_size(op2, |s| f(s));
        bool::for_each_size(imm, |s| f(s));
    }
}

impl<'a> SecretDep<'a> for RamInstr {
    type Decoded = RamInstr;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> RamInstr {
        RamInstr {
            opcode: u8::from_bits_iter(sizes, bits),
            dest: u8::from_bits_iter(sizes, bits),
            op1: u8::from_bits_iter(sizes, bits),
            op2: u64::from_bits_iter(sizes, bits),
            imm: bool::from_bits_iter(sizes, bits),
        }
    }
}



#[derive(Clone, Debug, Deserialize, Migrate, FromWireList)]
pub struct RamState {
    pub pc: u64,
    pub regs: Vec<u64>,
    #[serde(default = "panic_default")]
    pub tainted_regs: IfMode<AnyTainted, Vec<WordLabel>>,
    // All states parsed from the trace are assumed to be live.
    #[serde(default = "return_true")]
    pub live: bool,
    #[serde(default)]
    pub cycle: u32,
}

fn return_true() -> bool { true }

impl RamState {
    pub fn new(cycle: u32, pc: u32, regs: Vec<u32>, live: bool, tainted_regs: IfMode<AnyTainted, Vec<WordLabel>>) -> RamState {
        RamState {
            cycle,
            pc: pc as u64,
            regs: regs.into_iter().map(|x| x as u64).collect(),
            live,
            tainted_regs,
        }
    }

    pub fn default_with_regs(num_regs: usize) -> RamState {
        RamState {
            cycle: 0,
            pc: 0,
            regs: vec![0; num_regs],
            live: false,
            tainted_regs: IfMode::new(|_| vec![WORD_BOTTOM; num_regs]),
        }
    }
}

#[derive(Clone, Migrate)]
pub struct RamStateRepr<'a> {
    pub cycle: TWire<'a, u32>,
    pub pc: TWire<'a, u64>,
    pub regs: TWire<'a, Vec<u64>>,
    pub live: TWire<'a, bool>,
    pub tainted_regs: TWire<'a, IfMode<AnyTainted, Vec<WordLabel>>>,
}

impl<'a> Repr<'a> for RamState {
    type Repr = RamStateRepr<'a>;
}

impl<'a> Lit<'a> for RamState {
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        RamStateRepr {
            cycle: bld.lit(a.cycle),
            pc: bld.lit(a.pc),
            regs: bld.lit(a.regs),
            live: bld.lit(a.live),
            tainted_regs: TWire::new(a.tainted_regs.map(|regs| bld.lit(regs))),
        }
    }
}

impl<'a> LazySecret<'a> for RamState {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u64::expected_word_len(sizes) +
        Vec::<u64>::expected_word_len(sizes) +
        IfMode::<AnyTainted, Vec<WordLabel>>::expected_word_len(sizes) +
        bool::expected_word_len(sizes) +
        u32::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        let RamState { cycle, pc, ref regs, live, ref tainted_regs } = *self;
        pc.word_len() +
        regs.word_len() +
        tainted_regs.word_len() +
        live.word_len() +
        cycle.word_len()
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        let RamState { cycle, pc, ref regs, live, ref tainted_regs } = *self;
        pc.push_words(out);
        regs.push_words(out);
        tainted_regs.push_words(out);
        live.push_words(out);
        cycle.push_words(out);
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, RamState> for RamState
where
    C::Repr: Clone,
    u32: Mux<'a, C, u32, Output = u32>,
    <u32 as Repr<'a>>::Repr: Copy,
    u64: Mux<'a, C, u64, Output = u64>,
    <u64 as Repr<'a>>::Repr: Copy,
    WordLabel: Mux<'a, C, WordLabel, Output = WordLabel>,
    <WordLabel as Repr<'a>>::Repr: Copy,
    bool: Mux<'a, C, bool, Output = bool>,
    <bool as Repr<'a>>::Repr: Copy,
{
    type Output = RamState;

    fn mux(
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: Self::Repr,
        e: Self::Repr,
    ) -> Self::Repr {
        let c: TWire<C> = TWire::new(c);
        assert_eq!(t.regs.len(), e.regs.len());
        RamStateRepr {
            cycle: bld.mux(c.clone(), t.cycle, e.cycle),
            pc: bld.mux(c.clone(), t.pc, e.pc),
            regs: bld.mux(c.clone(), t.regs, e.regs),
            live: bld.mux(c.clone(), t.live, e.live),
            tainted_regs: bld.mux(c.clone(), t.tainted_regs, e.tainted_regs),
        }
    }
}

impl<'a> typed::Eq<'a, RamState> for RamState {
    type Output = bool;
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
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
            fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> { c.ty(TyKind::U8) }
            fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr.repr }
            fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                assert!(*w.ty == TyKind::U8);
                TWire::new(TWire::new(w))
            }
        }

        impl<'a> Lit<'a> for $Name {
            fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
                bld.lit(a as u8)
            }
        }

        impl<'a> typed::Eq<'a, $Name> for $Name {
            type Output = bool;
            fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
                bld.eq(a, b).repr
            }
        }

        impl<'a> typed::Ne<'a, $Name> for $Name {
            type Output = bool;
            fn ne(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
                bld.ne(a, b).repr
            }
        }

        impl<'a> FromEval<'a> for $Name {
            fn from_eval<E: Evaluator<'a> + ?Sized>(
                c: &CircuitBase<'a>,
                ev: &mut E,
                a: Self::Repr,
            ) -> Option<Self> {
                let raw = u8::from_eval(c, ev, a.repr)?;
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

        impl<'a> FromWireList<'a> for $Name {
            fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
                u8::expected_num_wires(sizes)
            }

            fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
                c: &C,
                sizes: &mut impl Iterator<Item = usize>,
                build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
            ) -> Self::Repr {
                TWire::new(u8::build_repr_from_wires(c, sizes, build_wire))
            }
        }

        impl<'a> LazySecret<'a> for $Name {
            fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
                u8::expected_word_len(sizes)
            }
            fn word_len(&self) -> usize {
                (*self as u8).word_len()
            }
            fn push_words(&self, out: &mut Vec<u32>) {
                (*self as u8).push_words(out);
            }
        }

        impl<'a> ToWireList<'a> for $Name {
            fn num_wires(x: &Self::Repr) -> usize {
                u8::num_wires(x)
            }
            fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
                u8::for_each_wire(x, f);
            }
            fn num_sizes(x: &Self::Repr) -> usize {
                u8::num_sizes(x)
            }
            fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {
                u8::for_each_size(x, f);
            }
        }

        impl<'a> SecretDep<'a> for $Name {
            type Decoded = Self;
            fn from_bits_iter(
                sizes: &mut impl Iterator<Item = usize>,
                bits: &mut impl Iterator<Item = Bits<'a>>,
            ) -> $Name {
                let raw = u8::from_bits_iter(sizes, bits);
                $Name::from_raw(raw).unwrap()
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

        /// Instructions used for taint analysis that signifies a value is written to a sink.
        /// The destination is unused, first argument is the value being output, and the second is the label of the output
        /// channel.
        Sink1 = 35,
        /// Instructions used for taint analysis that taints a value is with a given label.
        /// The destination is unused, the first argument is the register being tainted, and the second is the label.
        Taint1 = 39,

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

/// Labels are used to taint registers and memory ports.
/// Currently, labels only use the lower two bits. See the
/// [MicroRAM](https://gitlab-ext.galois.com/fromager/cheesecloth/MicroRAM/-/blob/dc22141c/src/Compiler/Tainted.hs#L27)
/// implementation for lattice details.
#[derive(Copy, Clone, Debug, Deserialize, Migrate)]
pub struct Label (
    #[serde(deserialize_with = "validate_label")]
    pub u8,
);
pub const BOTTOM: Label = Label(3);
pub const WORD_BOTTOM: WordLabel = WordLabel([BOTTOM;WORD_BYTES]);
pub const MAYBE_TAINTED: Label = Label(2);
pub const WORD_MAYBE_TAINTED: WordLabel = WordLabel([MAYBE_TAINTED;WORD_BYTES]);
pub const LABEL_BITS: u8 = 2;

/// Packed label representing 8 labels of the bytes of a word.
#[derive(Copy, Clone, Deserialize, Migrate)]
pub struct WordLabel ([Label; WORD_BYTES]);
// #[derive(Copy, Clone, Migrate)]
// pub struct WordLabelRepr<'a> (pub TWire<'a,[Label; WORD_BYTES]>);


pub fn valid_label(l:u8) -> bool {
    l <= BOTTOM.0
}

fn validate_label<'de, D>(d: D) -> Result<u8, D::Error>
    where D: de::Deserializer<'de>
{

    let value = u8::deserialize(d)?;

    if !valid_label(value) {
        return Err(de::Error::invalid_value(de::Unexpected::Unsigned(value as u64),
                                            &"a 2 bit label"));
    }

    Ok(value)
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a> Repr<'a> for Label {
    type Repr = Wire<'a>;
}

impl<'a> Flatten<'a> for Label {
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
        c.ty(TyKind::Uint(IntSize(LABEL_BITS as u16)))
    }

    fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        w.repr
    }

    fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(w)
    }
}

impl<'a> FromEval<'a> for Label {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Self::Repr,
    ) -> Option<Self> {
        let val = FromEval::from_eval(c, ev, a)?;
        Some(Label(val))
    }
}

// Cast u64 to Label.
impl<'a> Cast<'a, Label> for u64 {
    fn cast(bld: &impl Builder<'a>, x: Wire<'a>) -> Wire<'a> {
        let ty = <Label as Flatten>::wire_type(bld.circuit());
        bld.circuit().cast(x, ty)
    }
}

impl<'a> Cast<'a, u64> for Label {
    fn cast(bld: &impl Builder<'a>, x: Wire<'a>) -> Wire<'a> {
        bld.circuit().cast(x, bld.circuit().ty(TyKind::U64))
    }
}

impl<'a> Lit<'a> for Label {
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        assert!(valid_label(a.0));

        // bld.lit(a.0).repr
        // Lit::lit(bld, a.0)
        let ty = <Label as Flatten>::wire_type(bld.circuit());
        bld.circuit().lit(ty, a.0)
    }
}

impl<'a> Mux<'a, bool, Label> for Label {
    type Output = Label;

    fn mux(
        bld: &impl Builder<'a>,
        c: Wire<'a>,
        t: Wire<'a>,
        e: Wire<'a>,
    ) -> Wire<'a> {
        bld.circuit().mux(c, t, e)
    }
}

primitive_binary_impl!(Eq::eq(Label, Label) -> bool);
primitive_binary_impl!(Ne::ne(Label, Label) -> bool);
primitive_binary_impl!(Lt::lt(Label, Label) -> bool);
primitive_binary_impl!(Le::le(Label, Label) -> bool);
primitive_binary_impl!(Gt::gt(Label, Label) -> bool);
primitive_binary_impl!(Ge::ge(Label, Label) -> bool);

impl<'a> FromWireList<'a> for Label {
    fn expected_num_wires(_sizes: &mut impl Iterator<Item = usize>) -> usize { 1 }
    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        _sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        build_wire(Self::wire_type(c))
    }
}

impl<'a> LazySecret<'a> for Label {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u8::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        u8::word_len(&self.0)
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        u8::push_words(&self.0, out);
    }
}

impl<'a> ToWireList<'a> for Label {
    fn num_wires(x: &Self::Repr) -> usize { 1 }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        f(*x)
    }
    fn num_sizes(x: &Self::Repr) -> usize { 0 }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {}
}

impl<'a> SecretDep<'a> for Label {
    type Decoded = Label;
    fn from_bits_iter(
        _sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Label {
        let bits = bits.next().unwrap();
        let raw = bits.0.get(0).copied().unwrap_or(0) & ((1 << LABEL_BITS) - 1);
        Label(raw as u8)
    }
}

impl fmt::Debug for WordLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a> typed::Eq<'a, WordLabel> for WordLabel {
    type Output = bool;
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        let mut acc = bld.eq(a[0], b[0]);
        for (&a,&b) in a.iter().zip(b.iter()).skip(1) {
            acc = bld.and(acc, bld.eq(a,b));
        }
        *acc
    }
}

impl<'a> Repr<'a> for WordLabel {
    // type Repr = TWire<'a,[Label; WORD_BYTES]>; // WordLabelRepr<'a>;
    type Repr = <[Label; WORD_BYTES] as Repr<'a>>::Repr;
}

impl<'a> Lit<'a> for WordLabel {
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        <[Label; WORD_BYTES]>::lit(bld, a.0)
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, WordLabel> for WordLabel
where
    C::Repr: Clone,
    Label: Mux<'a, C, Label, Output = Label>,
{
    type Output = WordLabel;

    fn mux(
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: [TWire<'a, Label>; 8],
        e: [TWire<'a, Label>; 8],
    ) -> [TWire<'a, Label>; 8] {
        <[Label; WORD_BYTES] as Mux<'a, C, [Label; WORD_BYTES]>>::mux(bld, c, t, e)
    }
}

impl<'a> Flatten<'a> for WordLabel {
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
        <[Label; WORD_BYTES]>::wire_type(c)
    }

    fn to_wire(bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        <[Label; WORD_BYTES]>::to_wire(bld, TWire::new(w.repr))
    }

    fn from_wire(bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(<[Label; WORD_BYTES]>::from_wire(bld, w).repr)
    }
}

impl<'a> FromEval<'a> for WordLabel {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Self::Repr,
    ) -> Option<Self> {
        Some(WordLabel(<[Label; WORD_BYTES]>::from_eval(c, ev, a)?))
    }
}

impl<'a> FromWireList<'a> for WordLabel {
    fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        <[Label; WORD_BYTES]>::expected_num_wires(sizes)
    }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        <[Label; WORD_BYTES]>::build_repr_from_wires(c, sizes, build_wire)
    }
}

impl<'a> LazySecret<'a> for WordLabel {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        <[Label; WORD_BYTES]>::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        self.0.word_len()
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        self.0.push_words(out);
    }
}

impl<'a> ToWireList<'a> for WordLabel {
    fn num_wires(x: &Self::Repr) -> usize {
        <[Label; WORD_BYTES]>::num_wires(x)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        <[Label; WORD_BYTES]>::for_each_wire(x, f)
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        <[Label; WORD_BYTES]>::num_sizes(x)
    }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {
        <[Label; WORD_BYTES]>::for_each_size(x, f)
    }
}

impl<'a> SecretDep<'a> for WordLabel {
    type Decoded = WordLabel;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> WordLabel {
        WordLabel(<[Label; WORD_BYTES]>::from_bits_iter(sizes, bits))
    }
}


#[derive(Clone, Copy, Debug, FromWireList)]
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
    pub tainted: IfMode<AnyTainted, WordLabel>,
}

impl Default for MemPort {
    fn default() -> Self {
        MemPort {
            cycle:   MEM_PORT_UNUSED_CYCLE,
            addr:    u64::default(),
            value:   u64::default(),
            op:      MemOpKind::default(),
            width:   MemOpWidth::default(),
            tainted: IfMode::new(|_pf| WORD_BOTTOM),
        }
    }
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
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: TWire<'a, u8>,
        e: TWire<'a, u8>,
    ) -> TWire<'a, u8> {
        bld.mux(TWire::new(c), t, e)
    }
}


mk_named_enum! {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Migrate)]
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
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: TWire<'a, u8>,
        e: TWire<'a, u8>,
    ) -> TWire<'a, u8> {
        bld.mux(TWire::new(c), t, e)
    }
}

impl<'a> Cast<'a, u8> for MemOpWidth {
    fn cast(bld: &impl Builder<'a>, x: TWire<'a,u8>) -> Wire<'a> {
        let ty = <u8 as Flatten>::wire_type(bld.circuit());
        bld.circuit().cast(x.repr, ty)
    }
}

#[derive(Clone, Copy, Migrate)]
pub struct MemPortRepr<'a> {
    pub cycle: TWire<'a, u32>,
    pub addr: TWire<'a, u64>,
    pub value: TWire<'a, u64>,
    pub op: TWire<'a, MemOpKind>,
    pub width: TWire<'a, MemOpWidth>,
    pub tainted: TWire<'a, IfMode<AnyTainted, WordLabel>>,
}

impl<'a> Repr<'a> for MemPort {
    type Repr = MemPortRepr<'a>;
}

impl<'a> Lit<'a> for MemPort {
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        MemPortRepr {
            cycle: bld.lit(a.cycle),
            addr: bld.lit(a.addr),
            value: bld.lit(a.value),
            op: bld.lit(a.op),
            width: bld.lit(a.width),
            tainted: bld.lit(a.tainted),
        }
    }
}

impl<'a> LazySecret<'a> for MemPort {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u32::expected_word_len(sizes) +
        u64::expected_word_len(sizes) +
        u64::expected_word_len(sizes) +
        MemOpKind::expected_word_len(sizes) +
        MemOpWidth::expected_word_len(sizes) +
        IfMode::<AnyTainted, WordLabel>::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        let MemPort { cycle, addr, value, op, width, ref tainted } = *self;
        cycle.word_len() +
        addr.word_len() +
        value.word_len() +
        op.word_len() +
        width.word_len() +
        tainted.word_len()
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        let MemPort { cycle, addr, value, op, width, ref tainted } = *self;
        cycle.push_words(out);
        addr.push_words(out);
        value.push_words(out);
        op.push_words(out);
        width.push_words(out);
        tainted.push_words(out);
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, MemPort> for MemPort
where
    C::Repr: Clone,
    u16: Mux<'a, C, u16, Output = u16>,
    u32: Mux<'a, C, u32, Output = u32>,
    u64: Mux<'a, C, u64, Output = u64>,
    Label: Mux<'a, C, Label, Output = Label>,
    MemOpKind: Mux<'a, C, MemOpKind, Output = MemOpKind>,
    MemOpWidth: Mux<'a, C, MemOpWidth, Output = MemOpWidth>,
{
    type Output = MemPort;

    fn mux(
        bld: &impl Builder<'a>,
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
            tainted: bld.mux(c.clone(), t.tainted, e.tainted),
        }
    }
}


#[derive(Debug)]
pub struct CompareMemPort(MemPort);

impl PartialEq for CompareMemPort {
    fn eq(&self, other: &CompareMemPort) -> bool {
        let self_addr_masked = self.0.addr & !(MemOpWidth::WORD.bytes() as u64 - 1);
        let other_addr_masked = other.0.addr & !(MemOpWidth::WORD.bytes() as u64 - 1);
        self_addr_masked == other_addr_masked &&
        self.0.cycle == other.0.cycle
    }
}

impl cmp::Eq for CompareMemPort {}

impl PartialOrd for CompareMemPort {
    fn partial_cmp(&self, other: &CompareMemPort) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CompareMemPort {
    fn cmp(&self, other: &CompareMemPort) -> Ordering {
        let self_addr_masked = self.0.addr & !(MemOpWidth::WORD.bytes() as u64 - 1);
        let other_addr_masked = other.0.addr & !(MemOpWidth::WORD.bytes() as u64 - 1);
        let self_cycle_adj = self.0.cycle.wrapping_add(1);
        let other_cycle_adj = other.0.cycle.wrapping_add(1);
        self_addr_masked.cmp(&other_addr_masked)
            .then(self_cycle_adj.cmp(&other_cycle_adj))
    }
}

impl<'a> Repr<'a> for CompareMemPort {
    type Repr = MemPortRepr<'a>;
}

impl<'a> ToWireList<'a> for CompareMemPort {
    fn num_wires(x: &Self::Repr) -> usize {
        let MemPortRepr { ref cycle, ref addr, ref value, ref op, ref width, ref tainted } = *x;
        u32::num_wires(cycle) +
        u64::num_wires(addr) +
        u64::num_wires(value) +
        MemOpKind::num_wires(op) +
        MemOpWidth::num_wires(width) +
        IfMode::<AnyTainted, WordLabel>::num_wires(tainted)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        let MemPortRepr { ref cycle, ref addr, ref value, ref op, ref width, ref tainted } = *x;
        u32::for_each_wire(cycle, |w| f(w));
        u64::for_each_wire(addr, |w| f(w));
        u64::for_each_wire(value, |w| f(w));
        MemOpKind::for_each_wire(op, |w| f(w));
        MemOpWidth::for_each_wire(width, |w| f(w));
        IfMode::<AnyTainted, WordLabel>::for_each_wire(tainted, |w| f(w));
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        let MemPortRepr { ref cycle, ref addr, ref value, ref op, ref width, ref tainted } = *x;
        u32::num_sizes(cycle) +
        u64::num_sizes(addr) +
        u64::num_sizes(value) +
        MemOpKind::num_sizes(op) +
        MemOpWidth::num_sizes(width) +
        IfMode::<AnyTainted, WordLabel>::num_sizes(tainted)
    }
    fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
        let MemPortRepr { ref cycle, ref addr, ref value, ref op, ref width, ref tainted } = *x;
        u32::for_each_size(cycle, |s| f(s));
        u64::for_each_size(addr, |s| f(s));
        u64::for_each_size(value, |s| f(s));
        MemOpKind::for_each_size(op, |s| f(s));
        MemOpWidth::for_each_size(width, |s| f(s));
        IfMode::<AnyTainted, WordLabel>::for_each_size(tainted, |s| f(s));
    }
}

impl<'a> SecretDep<'a> for CompareMemPort {
    type Decoded = CompareMemPort;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> CompareMemPort {
        CompareMemPort(MemPort {
            cycle: u32::from_bits_iter(sizes, bits),
            addr: u64::from_bits_iter(sizes, bits),
            value: u64::from_bits_iter(sizes, bits),
            op: MemOpKind::from_bits_iter(sizes, bits),
            width: MemOpWidth::from_bits_iter(sizes, bits),
            tainted: IfMode::<AnyTainted, WordLabel>::from_bits_iter(sizes, bits),
        })
    }
}

impl<'a> Sortable<'a> for CompareMemPort {
    type Decoded = CompareMemPort;
    type AsSecretDep = Self;
    fn convert_vec(v: TWire<'a, Vec<Self>>) -> TWire<'a, Vec<Self>> { v }
}

impl<'a> Cast<'a, CompareMemPort> for MemPort {
    fn cast(_bld: &impl Builder<'a>, x: MemPortRepr<'a>) -> MemPortRepr<'a> {
        x
    }
}

impl<'a> Cast<'a, MemPort> for CompareMemPort {
    fn cast(_bld: &impl Builder<'a>, x: MemPortRepr<'a>) -> MemPortRepr<'a> {
        x
    }
}


#[derive(Debug)]
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
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
        c.ty(TyKind::Uint(IntSize(MemOpWidth::WORD.log_bytes() as u16)))
    }

    fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        w.repr
    }

    fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(w)
    }
}

impl<'a> Lit<'a> for ByteOffset {
    fn lit(bld: &impl Builder<'a>, x: Self) -> Wire<'a> {
        let c = bld.circuit();
        c.lit(Self::wire_type(c), x.raw() as u64)
    }
}

impl<'a> Mux<'a, bool, ByteOffset> for ByteOffset {
    type Output = ByteOffset;
    fn mux(bld: &impl Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        bld.circuit().mux(c, t, e)
    }
}


impl<'a> typed::Eq<'a, ByteOffset> for ByteOffset {
    type Output = bool;
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a, b)
    }
}

impl<'a> Cast<'a, u8> for ByteOffset {
    fn cast(bld: &impl Builder<'a>, x: Wire<'a>) -> Wire<'a> {
        bld.circuit().cast(x, bld.circuit().ty(TyKind::U8))
    }
}

impl<'a> FromEval<'a> for ByteOffset {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Self::Repr,
    ) -> Option<Self> {
        let val = FromEval::from_eval(c, ev, a)?;
        Some(ByteOffset(val))
    }
}

pub struct WordAddr;

impl<'a> Repr<'a> for WordAddr {
    type Repr = Wire<'a>;
}

impl<'a> Flatten<'a> for WordAddr {
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
        c.ty(TyKind::Uint(IntSize(
            MemOpWidth::WORD.bits() as u16 - MemOpWidth::WORD.log_bytes() as u16)))
    }

    fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        w.repr
    }

    fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(w)
    }
}

impl<'a> typed::Eq<'a, WordAddr> for WordAddr {
    type Output = bool;
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a, b)
    }
}


pub struct PackedMemPort;

#[derive(Clone, Copy, Migrate)]
pub struct PackedMemPortRepr<'a> {
    key: Wire<'a>,
    data: Wire<'a>,
}

impl PackedMemPort {
    pub fn from_unpacked<'a>(
        bld: &impl Builder<'a>,
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
        let data = bit_pack::concat_bits(bld, TWire::<(_, _, _, _, _)>::new((
            mp.value, mp.op, mp.width, mp.tainted, offset)));
        TWire::new(PackedMemPortRepr { key, data })
    }
}

impl<'a> PackedMemPortRepr<'a> {
    pub fn unpack(&self, bld: &impl Builder<'a>) -> TWire<'a, MemPort> {
        let (cycle_adj, waddr) = *bit_pack::split_bits::<(u32, WordAddr)>(bld, self.key);
        let cycle = bld.sub(cycle_adj, bld.lit(1));
        let (value, op, width, tainted, offset) =
            *bit_pack::split_bits::<(_, _, _, _, ByteOffset)>(bld, self.data);
        let addr = TWire::new(bit_pack::concat_bits(bld, TWire::<(_, _)>::new((offset, waddr))));
        TWire::new(MemPortRepr { cycle, addr, value, op, width, tainted })
    }
}

impl<'a> Repr<'a> for PackedMemPort {
    type Repr = PackedMemPortRepr<'a>;
}

impl<'a> Mux<'a, bool, PackedMemPort> for PackedMemPort {
    type Output = PackedMemPort;

    fn mux(
        bld: &impl Builder<'a>,
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
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a.key, b.key)
    }
}

impl<'a> typed::Lt<'a, PackedMemPort> for PackedMemPort {
    type Output = bool;
    fn lt(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().lt(a.key, b.key)
    }
}

impl<'a> typed::Le<'a, PackedMemPort> for PackedMemPort {
    type Output = bool;
    fn le(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
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

#[derive(Clone, Copy, Migrate)]
pub struct FetchPortRepr<'a> {
    pub addr: TWire<'a, u64>,
    pub instr: TWire<'a, RamInstr>,
    pub write: TWire<'a, bool>,
}

impl<'a> Repr<'a> for FetchPort {
    type Repr = FetchPortRepr<'a>;
}

impl<'a> Lit<'a> for FetchPort {
    fn lit(bld: &impl Builder<'a>, a: Self) -> Self::Repr {
        FetchPortRepr {
            addr: bld.lit(a.addr),
            instr: bld.lit(a.instr),
            write: bld.lit(a.write),
        }
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
        bld: &impl Builder<'a>,
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

#[derive(Clone, Copy, Migrate)]
pub struct PackedFetchPortRepr<'a> {
    key: Wire<'a>,
    data: Wire<'a>,
}

impl PackedFetchPort {
    pub fn from_unpacked<'a>(
        bld: &impl Builder<'a>,
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
    pub fn unpack(&self, bld: &impl Builder<'a>) -> TWire<'a, FetchPort> {
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
        bld: &impl Builder<'a>,
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
    fn eq(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().eq(a.key, b.key)
    }
}

impl<'a> typed::Lt<'a, PackedFetchPort> for PackedFetchPort {
    type Output = bool;
    fn lt(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().lt(a.key, b.key)
    }
}

impl<'a> typed::Le<'a, PackedFetchPort> for PackedFetchPort {
    type Output = bool;
    fn le(bld: &impl Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
        bld.circuit().le(a.key, b.key)
    }
}


pub struct CompareFetchPort(FetchPort);

impl PartialEq for CompareFetchPort {
    fn eq(&self, other: &CompareFetchPort) -> bool {
        self.0.addr == other.0.addr &&
        self.0.write == other.0.write
    }
}

impl cmp::Eq for CompareFetchPort {}

impl PartialOrd for CompareFetchPort {
    fn partial_cmp(&self, other: &CompareFetchPort) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CompareFetchPort {
    fn cmp(&self, other: &CompareFetchPort) -> Ordering {
        self.0.addr.cmp(&other.0.addr)
            .then(self.0.write.cmp(&other.0.write).reverse())
    }
}

impl<'a> Repr<'a> for CompareFetchPort {
    type Repr = FetchPortRepr<'a>;
}

impl<'a> ToWireList<'a> for CompareFetchPort {
    fn num_wires(x: &Self::Repr) -> usize {
        let FetchPortRepr { ref addr, ref instr, ref write } = *x;
        u64::num_wires(addr) +
        RamInstr::num_wires(instr) +
        bool::num_wires(write)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        let FetchPortRepr { ref addr, ref instr, ref write } = *x;
        u64::for_each_wire(addr, |w| f(w));
        RamInstr::for_each_wire(instr, |w| f(w));
        bool::for_each_wire(write, |w| f(w));
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        let FetchPortRepr { ref addr, ref instr, ref write } = *x;
        u64::num_sizes(addr) +
        RamInstr::num_sizes(instr) +
        bool::num_sizes(write)
    }
    fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
        let FetchPortRepr { ref addr, ref instr, ref write } = *x;
        u64::for_each_size(addr, |s| f(s));
        RamInstr::for_each_size(instr, |s| f(s));
        bool::for_each_size(write, |s| f(s));
    }
}

impl<'a> SecretDep<'a> for CompareFetchPort {
    type Decoded = CompareFetchPort;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> CompareFetchPort {
        CompareFetchPort(FetchPort {
            addr: u64::from_bits_iter(sizes, bits),
            instr: RamInstr::from_bits_iter(sizes, bits),
            write: bool::from_bits_iter(sizes, bits),
        })
    }
}

impl<'a> Sortable<'a> for CompareFetchPort {
    type Decoded = CompareFetchPort;
    type AsSecretDep = Self;
    fn convert_vec(v: TWire<'a, Vec<Self>>) -> TWire<'a, Vec<Self>> { v }
}

impl<'a> Cast<'a, CompareFetchPort> for FetchPort {
    fn cast(_bld: &impl Builder<'a>, x: FetchPortRepr<'a>) -> FetchPortRepr<'a> {
        x
    }
}

impl<'a> Cast<'a, FetchPort> for CompareFetchPort {
    fn cast(_bld: &impl Builder<'a>, x: FetchPortRepr<'a>) -> FetchPortRepr<'a> {
        x
    }
}




#[derive(Clone, Debug)]
pub struct VersionedMultiExec{
    pub version: Version,
    /// The set of all enabled features.  This is built by combining `declared_features` with the
    /// baseline features implied by `version`.
    pub features: HashSet<Feature>,
    /// The set of features explicitly declared in the version header.
    pub declared_features: HashSet<Feature>,

    pub inner: MultiExec,
}

impl VersionedMultiExec {
    // Checks if the executions have the given feature.
    // All internal, executions have the same features by construction.
    pub fn has_feature(&self, feature: Feature) -> bool {
        self.features.contains(&feature)
    }
    pub fn validate(&self) -> Result<(), String> {
        self.inner.validate(&self.features)
    }
}

#[derive(Clone, Debug, Deserialize)]
pub struct MultiExec {
    pub execs: HashMap<String, ExecBody>,
    pub mem_equiv: Vec<MemoryEquivalence>,
}

impl MultiExec {
    pub fn validate(&self, features: &HashSet<Feature>) -> Result<(), String> {
        for (_, exec) in self.execs.iter() { 
            exec.validate(features).unwrap();
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct ExecBody {
    pub program: Vec<RamInstr>,
    pub init_mem: Vec<MemSegment>,
    pub params: Params,
    pub segments: Vec<Segment>,
    pub trace: Vec<TraceChunk>,
    pub advice: HashMap<u64, Vec<Advice>>,
}

impl ExecBody {
    pub fn initial_state(&self) -> RamState {
        let mut regs = vec![0; self.params.num_regs];
        regs[0] = self.init_mem.iter()
            .filter(|ms| ms.heap_init == false)
            .map(|ms| ms.start + ms.len)
            .max().unwrap_or(0);
        let tainted_regs = IfMode::new(|_| vec![WORD_BOTTOM; self.params.num_regs]);
        RamState { cycle: 0, pc: 0, regs, live: true, tainted_regs }
    }

    pub fn validate(&self, features: &HashSet<Feature>) -> Result<(), String> {
        let params = &self.params;
        if !features.contains(&Feature::PublicPc) {
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
            if !features.contains(&Feature::PublicPc) {
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
            if i > trace_len { // account for the advice converted into post-state indices (so > instead of >=)
                return Err(format!(
                    "`advice` key out of range: the index is {} but `trace` has only {} states",
                    i, trace_len,
                ));
            }
        }
        Ok(())
    }
}

pub type MemoryEquivalence = Vec<(String, String)>;

#[derive(Clone, Debug, Deserialize)]
pub struct MemSegment {
    pub start: u64,
    pub len: u64,
    pub read_only: bool,
    pub secret: bool,
    /// Whether the segment is used to initialize the heap. Defaults to `false` if field is
    /// missing.
    #[serde(default="bool::default")]
    pub heap_init: bool,
    #[serde(default)]
    pub data: Vec<u64>,
    #[serde(default = "panic_default")]
    pub tainted: IfMode<AnyTainted,Vec<WordLabel>>,
    #[serde(default)]
    pub name: String,
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

    pub fn desc(&self) -> &'static str {
        if self.init_pc().is_some() {
            "public"
        } else {
            "secret"
        }
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
        tainted: IfMode<AnyTainted,WordLabel>,
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

pub struct TaintCalcIntermediate<'a> {
    pub label_x: TWire<'a,WordLabel>,      // Tainted label for x.
    pub label_y_joined: TWire<'a,Label>,   // Joined labels for y.
    pub label_result: TWire<'a,WordLabel>, // Tainted label for result.
    pub addr_offset: TWire<'a,ByteOffset>, // Offset of memory address.
}

pub struct CalcIntermediate<'a> {
    pub x: TWire<'a,u64>,
    pub y: TWire<'a,u64>,
    pub result: TWire<'a,u64>,
    pub tainted: IfMode<AnyTainted, TaintCalcIntermediate<'a>>,
    /// If set, then this step is publicly known not to use any `MemPort`.
    pub mem_port_unused: bool,
}

