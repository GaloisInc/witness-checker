use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::mem;
use serde::de::{self, Deserializer, SeqAccess, MapAccess, Visitor};
use serde::Deserialize;
use crate::micro_ram::types::{
    Execution, Params, Opcode, MemOpKind, MemOpWidth, RamInstr, Advice, TraceChunk,
    Segment, SegmentConstraint,
};
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
pub struct ParseExecution(VersionedExecution);

impl ParseExecution {
    pub fn into_inner(self) -> Execution {
        self.0.0
    }
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


impl<'de> Deserialize<'de> for Execution {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_struct(
            "Execution",
            &["program", "init_mem", "params", "trace", "advice"],
            ExecutionVisitor,
        )
    }
}

struct ExecutionVisitor;
impl<'de> Visitor<'de> for ExecutionVisitor {
    type Value = Execution;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "an execution object")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Execution, A::Error> {
        let mut ex = Execution {
            version: Version::default(),
            features: HashSet::new(),
            declared_features: HashSet::new(),

            program: Vec::new(),
            init_mem: Vec::new(),
            params: Params::default(),
            segments: Vec::new(),
            trace: Vec::new(),
            advice: HashMap::new(),
        };

        let mut seen = HashSet::new();
        while let Some(k) = map.next_key::<String>()? {
            if !seen.insert(k.clone()) {
                return Err(serde::de::Error::custom(format_args!(
                    "duplicate key {:?}", k,
                )));
            }

            match &k as &str {
                "program" => { ex.program = map.next_value()?; },
                "init_mem" => { ex.init_mem = map.next_value()?; },
                "params" => { ex.params = map.next_value()?; },
                "segments" if has_feature(Feature::PublicPc) => {
                    ex.segments = map.next_value()?;
                },
                "trace" => {
                    if has_feature(Feature::PublicPc) {
                        ex.trace = map.next_value()?;
                    } else {
                        ex.trace = vec![TraceChunk {
                            segment: 0,
                            states: map.next_value()?,
                            debug: None,
                        }];
                    }
                },
                "advice" => {
                    ex.advice = map.next_value()?;
                    if has_feature(Feature::PreAdvice) {
                        // Convert from pre-state indices to post-state indices.
                        ex.advice = mem::take(&mut ex.advice).into_iter()
                            .map(|(k, v)| (k + 1, v)).collect();
                    }
                },
                _ => return Err(serde::de::Error::custom(format_args!(
                    "unknown key {:?}", k,
                ))),
            }
        }

        Ok(ex)
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


impl<'de> Deserialize<'de> for Segment {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_any(SegmentVisitor)
    }
}

struct SegmentVisitor;
impl<'de> Visitor<'de> for SegmentVisitor {
    type Value = Segment;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a segment object")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Segment, A::Error> {
        let mut x = Segment {
            constraints: Vec::new(),
            len: 0,
            successors: Vec::new(),
            enter_from_network: false,
            exit_to_network: false,
        };

        let mut seen = HashSet::new();
        while let Some(k) = map.next_key::<String>()? {
            if !seen.insert(k.clone()) {
                return Err(serde::de::Error::custom(format_args!(
                    "duplicate key {:?}", k,
                )));
            }

            match &k as &str {
                "constraints" => { x.constraints = map.next_value()?; },
                "len" => { x.len = map.next_value()?; },
                "successors" => { x.successors = map.next_value()?; },
                "enter_from_network" => { x.enter_from_network = map.next_value()?; },
                "exit_to_network" => { x.exit_to_network = map.next_value()?; },
                _ => return Err(serde::de::Error::custom(format_args!(
                    "unknown key {:?}", k,
                ))),
            }
        }

        Ok(x)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<Segment, A::Error> {
        let mut seq = CountedSeqAccess::new(seq, 5);
        let x = Segment {
            constraints: seq.next_element()?,
            len: seq.next_element()?,
            successors: seq.next_element()?,
            enter_from_network: seq.next_element()?,
            exit_to_network: seq.next_element()?,
        };
        seq.finish()?;
        Ok(x)
    }
}

impl<'de> Deserialize<'de> for SegmentConstraint {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_seq(SegmentConstraintVisitor)
    }
}

struct SegmentConstraintVisitor;
impl<'de> Visitor<'de> for SegmentConstraintVisitor {
    type Value = SegmentConstraint;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a segment constraint object")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<SegmentConstraint, A::Error> {
        let mut seq = CountedSeqAccess::new(seq, 1);
        let x = match &seq.next_element::<String>()? as &str {
            "pc" => {
                seq.expect += 1;
                let pc = seq.next_element()?;
                SegmentConstraint::Pc(pc)
            },
            kind => return Err(de::Error::custom(
                format_args!("unknown segment constraint kind {}", kind),
            )),
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
