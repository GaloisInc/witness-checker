use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use serde::de::{self, Deserializer, SeqAccess, Visitor};
use serde::Deserialize;
use crate::ir::typed::{self, Builder, TWire, Repr, Lit, Secret, Mux};


/// A TinyRAM instruction.  The program itself is not secret, but we most commonly load
/// instructions from secret indices, which results in a secret instruction.
#[derive(Clone, Copy, Debug, Default)]
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

impl<'a> Secret<'a> for RamInstr {
    fn secret(bld: &Builder<'a>, a: Option<Self>) -> Self::Repr {
        if let Some(a) = a {
            RamInstrRepr {
                opcode: bld.secret(Some(a.opcode)),
                dest: bld.secret(Some(a.dest)),
                op1: bld.secret(Some(a.op1)),
                op2: bld.secret(Some(a.op2)),
                imm: bld.secret(Some(a.imm)),
            }
        } else {
            RamInstrRepr {
                opcode: bld.secret(None),
                dest: bld.secret(None),
                op1: bld.secret(None),
                op2: bld.secret(None),
                imm: bld.secret(None),
            }
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
    pub flag: bool,
}

impl RamState {
    pub fn new(pc: u32, regs: Vec<u32>, flag: bool) -> RamState {
        RamState {
            pc: pc as u64,
            regs: regs.into_iter().map(|x| x as u64).collect(),
            flag,
        }
    }
}

#[derive(Clone)]
pub struct RamStateRepr<'a> {
    pub pc: TWire<'a, u64>,
    pub regs: Vec<TWire<'a, u64>>,
    pub flag: TWire<'a, bool>,
}

impl<'a> Repr<'a> for RamState {
    type Repr = RamStateRepr<'a>;
}

impl<'a> Lit<'a> for RamState {
    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        RamStateRepr {
            pc: bld.lit(a.pc),
            regs: bld.lit(a.regs).repr,
            flag: bld.lit(a.flag),
        }
    }
}

impl RamState {
    pub fn secret_with_value<'a>(bld: &Builder<'a>, a: Self) -> TWire<'a, RamState> {
        TWire::new(RamStateRepr {
            pc: bld.secret(Some(a.pc)),
            regs: a.regs.iter().map(|&x| bld.secret(Some(x))).collect(),
            flag: bld.secret(Some(a.flag)),
        })
    }

    pub fn secret_with_len<'a>(bld: &Builder<'a>, len: usize) -> TWire<'a, RamState> {
        TWire::new(RamStateRepr {
            pc: bld.secret(None),
            regs: (0 .. len).map(|_| bld.secret(None)).collect(),
            flag: bld.secret(None),
        })
    }
}


macro_rules! mk_named_enum {
    (
        $(#[$attr:meta])*
        $vis:vis enum $Name:ident {
            $($Variant:ident = $value:expr,)*
        }
    ) => {
        $(#[$attr])*
        #[repr(u8)]
        $vis enum $Name {
            $($Variant = $value,)*
        }

        impl $Name {
            pub fn from_raw(x: u8) -> Option<$Name> {
                Some(match x {
                    $($value => $Name::$Variant,)*
                    _ => return None,
                })
            }

            pub fn count() -> usize {
                0 $(+ { drop($Name::$Variant); 1})*
            }

            pub fn iter() -> impl Iterator<Item = $Name> {
                (0 .. Self::count() as u8).map(|i| Self::from_raw(i).unwrap())
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

        impl<'a> Lit<'a> for $Name {
            fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
                bld.lit(a as u8)
            }
        }

        impl<'a> Secret<'a> for $Name {
            fn secret(bld: &Builder<'a>, a: Option<Self>) -> Self::Repr {
                bld.secret(a.map(|a| a as u8))
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
    };
}

mk_named_enum! {
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

        Store = 23,
        Load = 24,

        Read = 25,
        Answer = 26,

        Advise = 27,
    }
}


pub const MEM_PORT_UNUSED_CYCLE: u32 = !0 - 1;
pub const MEM_PORT_PRELOAD_CYCLE: u32 = !0;

#[derive(Clone, Copy, Default)]
pub struct MemPort {
    pub cycle: u32,
    pub addr: u64,
    pub value: u64,
    pub op: MemOpKind,
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

#[derive(Clone, Copy)]
pub struct MemPortRepr<'a> {
    pub cycle: TWire<'a, u32>,
    pub addr: TWire<'a, u64>,
    pub value: TWire<'a, u64>,
    pub op: TWire<'a, MemOpKind>,
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
                op: bld.secret(Some(a.op)),
            }
        } else {
            MemPortRepr {
                cycle: bld.secret(None),
                addr: bld.secret(None),
                value: bld.secret(None),
                op: bld.secret(None),
            }
        }
    }
}

impl<'a, C: Repr<'a>> Mux<'a, C, MemPort> for MemPort
where
    C::Repr: Clone,
    u32: Mux<'a, C, u32, Output = u32>,
    u64: Mux<'a, C, u64, Output = u64>,
    MemOpKind: Mux<'a, C, MemOpKind, Output = MemOpKind>,
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
        }
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
    fn secret(bld: &Builder<'a>, a: Option<Self>) -> Self::Repr {
        if let Some(a) = a {
            FetchPortRepr {
                addr: bld.secret(Some(a.addr)),
                instr: bld.secret(Some(a.instr)),
                write: bld.secret(Some(a.write)),
            }
        } else {
            FetchPortRepr {
                addr: bld.secret(None),
                instr: bld.secret(None),
                write: bld.secret(None),
            }
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


#[derive(Clone, Debug, Deserialize)]
pub struct Execution {
    pub program: Vec<RamInstr>,
    #[serde(default)]
    pub init_mem: Vec<u64>,
    pub params: Params,
    pub trace: Vec<RamState>,
    #[serde(default)]
    pub advice: HashMap<u64, Vec<Advice>>,
}

impl Execution {
    pub fn validate(self) -> Result<Self, String> {
        let params = &self.params;
        if self.trace.len() > params.trace_len {
            return Err(format!(
                "`trace` contains more than `trace_len` states: {} > {}",
                self.trace.len(), params.trace_len,
            ));
        }

        for (i, s) in self.trace.iter().enumerate() {
            if s.regs.len() != params.num_regs {
                return Err(format!(
                    "`trace[{}]` should have {} register values (`num_regs`), not {}",
                    i, params.num_regs, s.regs.len(),
                ));
            }
        }

        for &i in self.advice.keys() {
            let i = usize::try_from(i)
                .map_err(|e| format!("advice key {} out of range: {}", i, e))?;
            if i >= self.params.trace_len {
                return Err(format!(
                    "`advice` key out of range: the index is {} but `trace_len` is {}",
                    i, self.params.trace_len,
                ));
            }
        }

        Ok(self)
    }
}

#[derive(Clone, Debug, Deserialize)]
pub struct Params {
    pub num_regs: usize,
    pub trace_len: usize,
}

#[derive(Clone, Debug)]
pub enum Advice {
    MemOp { addr: u64, value: u64, op: MemOpKind },
    Stutter,
    Advise { advise: u64 },
}


impl<'de> Deserialize<'de> for Opcode {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        match Opcode::from_str(&s) {
            Some(x) => Ok(x),
            None => Err(de::Error::invalid_value(
                de::Unexpected::Str(&s),
                &"a MicroRAM opcode mnemonic",
            )),
        }
    }
}

impl<'de> Deserialize<'de> for MemOpKind {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        match MemOpKind::from_str(&s) {
            Some(x) => Ok(x),
            None => Err(de::Error::invalid_value(
                de::Unexpected::Str(&s),
                &"a memory op kind",
            )),
        }
    }
}


impl<'de> Deserialize<'de> for RamInstr {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_tuple(5, RamInstrVisitor)
    }
}

struct RamInstrVisitor;
impl<'de> Visitor<'de> for RamInstrVisitor {
    type Value = RamInstr;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a sequence of 5 values")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<RamInstr, A::Error> {
        let mut seq = CountedSeqAccess::new(seq, 5);
        let x = RamInstr {
            opcode: seq.next_element::<Opcode>()? as u8,
            dest: seq.next_element::<Option<u64>>()?.unwrap_or(0),
            op1: seq.next_element::<Option<u64>>()?.unwrap_or(0),
            imm: seq.next_element::<Option<bool>>()?.unwrap_or(false),
            op2: seq.next_element::<Option<u64>>()?.unwrap_or(0),
        };
        seq.finish()?;
        Ok(x)
    }
}


impl<'de> Deserialize<'de> for Advice {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_seq(AdviceVisitor)
    }
}

struct AdviceVisitor;
impl<'de> Visitor<'de> for AdviceVisitor {
    type Value = Advice;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "an advice object")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<Advice, A::Error> {
        let mut seq = CountedSeqAccess::new(seq, 1);
        let x = match &seq.next_element::<String>()? as &str {
            "MemOp" => {
                seq.expect += 3;
                Advice::MemOp {
                    addr: seq.next_element()?,
                    value: seq.next_element()?,
                    op: seq.next_element()?,
                }
            },
            "Stutter" => {
                Advice::Stutter
            },
            "Advise" => {
                seq.expect += 1;
                Advice::Advise {
                    advise: seq.next_element()?,
                }
            },
            kind => return Err(de::Error::custom(
                format_args!("unknown advice kind {}", kind),
            )),
        };
        seq.finish()?;
        Ok(x)
    }
}


struct CountedSeqAccess<A> {
    seq: A,
    expect: usize,
    seen: usize,
}

impl<'de, A: SeqAccess<'de>> CountedSeqAccess<A> {
    fn new(seq: A, expect: usize) -> CountedSeqAccess<A> {
        CountedSeqAccess { seq, expect, seen: 0 }
    }

    fn next_element<T: Deserialize<'de>>(&mut self) -> Result<T, A::Error> {
        assert!(self.seen < self.expect);
        match self.seq.next_element::<T>()? {
            Some(x) => {
                self.seen += 1;
                Ok(x)
            },
            None => {
                return Err(de::Error::invalid_length(
                    self.seen, 
                    &(&format!("a sequence of length {}", self.expect) as &str),
                ));
            },
        }
    }

    fn finish(mut self) -> Result<(), A::Error> {
        match self.seq.next_element::<()>() {
            Ok(None) => Ok(()),
            // A parse error indicates there was some data left to parse - there shouldn't be.
            Ok(Some(_)) | Err(_) => {
                return Err(de::Error::invalid_length(
                    self.seen + 1,
                    &(&format!("a sequence of length {}", self.expect) as &str),
                ));
            },
        }
    }
}
