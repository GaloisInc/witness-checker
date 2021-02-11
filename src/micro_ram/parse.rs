use std::cell::Cell;
use std::collections::HashSet;
use std::fmt;
use std::mem;
use serde::de::{self, Deserializer, SeqAccess, Visitor};
use serde::Deserialize;
use crate::micro_ram::types::{Execution, Opcode, MemOpKind, MemOpWidth, RamInstr, Advice};
use crate::micro_ram::feature::{self, Feature, Version};


thread_local! {
    static FEATURES: Cell<HashSet<Feature>> = Cell::new(HashSet::new());
}

pub fn has_feature(f: Feature) -> bool {
    FEATURES.with(|c| {
        let features = c.replace(HashSet::new());
        let r = features.contains(&f);
        c.set(features);
        r
    })
}

struct FeaturesGuard {
    old: HashSet<Feature>,
}

impl FeaturesGuard {
    pub fn set(fs: HashSet<Feature>) -> FeaturesGuard {
        FEATURES.with(|c| {
            let old = c.replace(fs);
            FeaturesGuard { old }
        })
    }
}

impl Drop for FeaturesGuard {
    fn drop(&mut self) {
        let old = mem::replace(&mut self.old, HashSet::new());
        FEATURES.with(|c| c.set(old))
    }
}

pub fn with_features<R>(fs: HashSet<Feature>, f: impl FnOnce() -> R) -> R {
    let _g = FeaturesGuard::set(fs);
    f()
}


/// A wrapper around `Execution` to support custom parsing logic.
#[derive(Deserialize)]
#[serde(transparent)]
pub struct ParseExecution(AnyExecution);

impl ParseExecution {
    pub fn into_inner(self) -> Execution {
        match self.0 {
            AnyExecution::Versioned(e) => e.0,
            AnyExecution::Unversioned(e) => e.0,
        }
    }
}



#[derive(Deserialize)]
#[serde(untagged)]
enum AnyExecution {
    Versioned(VersionedExecution),
    Unversioned(UnversionedExecution),
}


/// Newtype wrapper around `Execution` that reads a version number and then deserializes according
/// to that version.
pub struct VersionedExecution(Execution);

impl<'de> Deserialize<'de> for VersionedExecution {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_tuple(3, VersionedExecutionVisitor)
    }
}

struct VersionedExecutionVisitor;
impl<'de> Visitor<'de> for VersionedExecutionVisitor {
    type Value = VersionedExecution;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a sequence of 3 items")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<VersionedExecution, A::Error> {
        let mut seq = CountedSeqAccess::new(seq, 3);
        let ver = seq.next_element::<Version>()?;
        let features = seq.next_element::<HashSet<Feature>>()?;
        let ver_features = match feature::lookup_version(ver) {
            Some(x) => x,
            None => return Err(serde::de::Error::custom(format_args!(
                "input has unsupported version {:?}", ver
            ))),
        };
        let all_features = &features | &ver_features;
        let exec = with_features(all_features.clone(), || {
            seq.next_element::<Execution>()
        })?;
        seq.finish()?;
        Ok(VersionedExecution(Execution {
            version: ver,
            features: all_features,
            declared_features: features,
            .. exec
        }))
    }
}


/// Newtype wrapper around `Execution` that expects no version number wrapper and deserializes
/// according to the current version.
pub struct UnversionedExecution(Execution);

impl<'de> Deserialize<'de> for UnversionedExecution {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let mut exec = Execution::deserialize(d)?;
        Ok(UnversionedExecution(exec))
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

impl<'de> Deserialize<'de> for MemOpWidth {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let w = u8::deserialize(d)?;
        match w {
            1 => Ok(MemOpWidth::W1),
            2 => Ok(MemOpWidth::W2),
            4 => Ok(MemOpWidth::W4),
            8 => Ok(MemOpWidth::W8),
            _ => Err(de::Error::invalid_value(
                de::Unexpected::Unsigned(w as _),
                &"a memory op width",
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
                seq.expect += 4;
                Advice::MemOp {
                    addr: seq.next_element()?,
                    value: seq.next_element()?,
                    op: seq.next_element()?,
                    width: seq.next_element()?,
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
