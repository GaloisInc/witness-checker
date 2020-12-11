use std::fmt;
use serde::de::{self, Deserializer, SeqAccess, Visitor};
use serde::Deserialize;
use crate::micro_ram::types::{Execution, Opcode, MemOpKind, RamInstr, Advice};


/// A wrapper around `Execution` to support custom parsing logic.
#[derive(Deserialize)]
#[serde(transparent)]
pub struct ParseExecution(Execution);

impl ParseExecution {
    pub fn into_inner(self) -> Execution {
        self.0
    }
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
            dest: seq.next_element::<Option<u8>>()?.unwrap_or(0),
            op1: seq.next_element::<Option<u8>>()?.unwrap_or(0),
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
