use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::mem;
use serde::de::{self, Deserializer, SeqAccess, MapAccess, Visitor};
use serde::Deserialize;
use crate::micro_ram::types::{
    VersionedMultiExec, MultiExec, ExecBody, Params, Opcode, MemOpKind, MemOpWidth, RamInstr,
    RamState, Advice, Trace, InstrTrace, BbmdTrace, TraceChunk, BbmdTraceChunk, Segment,
    SegmentConstraint, BbmdBlock, Commitment, CodeSegment,
};
use crate::micro_ram::feature::{self, Feature, Version};
use crate::mode::if_mode::{AnyTainted, IfMode, is_mode};


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

impl<'de> Deserialize<'de> for VersionedMultiExec {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_tuple(3, VersionedMultiExecVisitor)
    }
}


struct VersionedMultiExecVisitor;
impl<'de> Visitor<'de> for VersionedMultiExecVisitor {
    type Value = VersionedMultiExec;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a sequence of 3 items")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<VersionedMultiExec, A::Error> {
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
        if all_features.contains(&Feature::Buggy) {
            let mut features_list = features.iter().cloned().collect::<Vec<_>>();
            features_list.sort();
            eprintln!(
                "warning: file version {} +{:?} comes from a generator with known bugs",
                ver, features_list,
            );
        }
        let inner = with_features(all_features.clone(), || {
            if has_feature(Feature::MultiExec) {
                seq.next_element::<MultiExec>()
            } else {
                let body = seq.next_element::<ExecBody>()?;
                let mut execs = HashMap::new();
                execs.insert("".to_string(),body);
                Ok(MultiExec {
                    execs: execs,
                    mem_equiv: Vec::new()
                })
            }
        })?;
        seq.finish()?;
        Ok(VersionedMultiExec {
            version: ver,
            features: all_features,
            declared_features: features,
            inner: inner
        })
    }
}

impl<'de> Deserialize<'de> for ExecBody {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_struct(
            "ExecBody",
            &["program", "init_mem", "params", "trace", "advice"],
            ExecBodyVisitor,
        )
    }
}

struct ExecBodyVisitor;
impl<'de> Visitor<'de> for ExecBodyVisitor {
    type Value = ExecBody;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "an execution object")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<ExecBody, A::Error> {
        let mut ex = ExecBody {
            program: Vec::new(),
            init_mem: Vec::new(),
            params: Params::default(),
            // Dummy trace, to be replaced after `it`/`bt` is populated.
            trace: Trace::Instr(InstrTrace::default()),
            advice: HashMap::new(),
            labels: HashMap::new(),
            provided_init_state: None,
        };
        let mut trace = None;

        let mut instr_segments = None;
        let mut bbmd_blocks = None;

        let mut seen = HashSet::new();
        while let Some(k) = map.next_key::<String>()? {
            if !seen.insert(k.clone()) {
                return Err(serde::de::Error::custom(format_args!(
                    "duplicate key {:?}", k,
                )));
            }

            match &k as &str {
                "program" => {
                    if has_feature(Feature::CodeSegments) {
                        ex.program = map.next_value()?;
                    } else {
                        let instrs: Vec<_> = map.next_value()?;
                        ex.program = vec![CodeSegment {
                            name: "_program".into(),
                            start: 0,
                            len: instrs.len() as u64,
                            secret: false,
                            uncommitted: false,
                            instrs,
                        }];
                    }
                },
                "init_mem" => { ex.init_mem = map.next_value()?; },
                "params" => { ex.params = map.next_value()?; },

                "segments" => {
                    instr_segments = Some(map.next_value::<Vec<Segment>>()?);
                },
                "bbmd_blocks" => {
                    bbmd_blocks = Some(map.next_value::<Vec<BbmdBlock>>()?);
                },

                "trace" => {
                    // We don't know which trace mode to expect until we've seen `params`, which
                    // could come later in the input.  But the three trace forms are mutually
                    // exclusive, so we try parsing in each mode and see which one works.
                    trace = Some(map.next_value::<AnyTrace>()?);
                },

                "advice" => {
                    ex.advice = map.next_value()?;
                    if has_feature(Feature::PreAdvice) {
                        // Convert from pre-state indices to post-state indices.
                        ex.advice = mem::take(&mut ex.advice).into_iter()
                            .map(|(k, v)| (k + 1, v)).collect();
                    }
                },
                "labels" => {
                    ex.labels = map.next_value()?;
                },
                // Note: `provided_init_state` can't be set in the CBOR file.
                _ => return Err(serde::de::Error::custom(format_args!(
                    "unknown key {:?}", k,
                ))),
            }
        }

        let trace = trace.ok_or_else(|| serde::de::Error::custom("missing key `trace`"))?;

        ex.trace = if has_feature(Feature::Bbmd) && ex.params.bbmd {
            Trace::Bbmd(BbmdTrace {
                blocks: bbmd_blocks.take().ok_or_else(|| serde::de::Error::custom(
                    "missing key `bbmd_blocks` for BBMD execution"))?,
                chunks: match trace {
                    AnyTrace::Bbmd(x) => x,
                    AnyTrace::Ambiguous(pairs) => pairs.into_iter()
                        .map(|(block_idx, states)| BbmdTraceChunk { block_idx, states })
                        .collect(),
                    _ => return Err(serde::de::Error::custom(
                        "bad `trace` format for BBMD execution")),
                },
            })
        } else if has_feature(Feature::PublicPc) {
            Trace::Instr(InstrTrace {
                segments: instr_segments.take().ok_or_else(|| serde::de::Error::custom(
                    "missing key `segments` for public PC execution"))?,
                chunks: match trace {
                    AnyTrace::Instr(x) => x,
                    AnyTrace::Ambiguous(pairs) => pairs.into_iter()
                        .map(|(segment, states)| TraceChunk { segment, states, debug: None })
                        .collect(),
                    _ => return Err(serde::de::Error::custom(
                        "bad `trace` format for public PC execution")),
                },
            })
        } else {
            // Adjust flat traces to fit the public-pc format.  In flat mode, the prover can
            // provide an initial state, with some restrictions.
            let states = match trace {
                AnyTrace::Flat(x) => x,
                _ => return Err(serde::de::Error::custom(
                    "bad `trace` format for flat execution")),
            };


            let new_segment = Segment {
                constraints: vec![],
                len: ex.params.trace_len.unwrap() - 1,
                successors: vec![],
                enter_from_network: false,
                exit_to_network: false,
            };

            let provided_init_state = Some(states[0].clone());
            let new_chunk = TraceChunk {
                segment: 0,
                states: states[1..].to_owned(),
                debug: None,
            };

            ex.provided_init_state = provided_init_state;
            Trace::Instr(InstrTrace {
                segments: vec![new_segment],
                chunks: vec![new_chunk],
            })
        };

        // The cases above that use these fields call `take()`, so they should all be `None` by
        // this point.
        if instr_segments.is_some() {
            return Err(serde::de::Error::custom(
                "key `segments` is unexpected in the current execution mode"));
        }
        if bbmd_blocks.is_some() {
            return Err(serde::de::Error::custom(
                "key `bbmd_blocks` is unexpected in the current execution mode"));
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

        let opcode = seq.next_element::<Opcode>()? as u8;
        let dest = seq.next_element::<Option<u8>>()?;
        let op1 = seq.next_element::<Option<u8>>()?;
        let mut imm = seq.next_element::<Option<bool>>()?;
        let mut op2 = seq.next_element::<Option<u64>>()?;

        if !has_feature(Feature::AdviseMaxBound) {
            if opcode == Opcode::Advise as u8 {
                // Set the upper bound to the maximum possible value, meaning the instruction can
                // produce any value.
                imm = Some(true);
                op2 = Some(u64::MAX);
            }
        }

        let x = RamInstr {
            opcode,
            dest: dest.unwrap_or(0),
            op1: op1.unwrap_or(0),
            imm: imm.unwrap_or(false),
            op2: op2.unwrap_or(0),
        };
        seq.finish()?;
        Ok(x)
    }
}


impl<'de> Deserialize<'de> for Commitment {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        let i = s.find(':').ok_or_else(|| de::Error::invalid_value(
            de::Unexpected::Str(&s),
            &"a commitment of the form KIND:DATA",
        ))?;

        let kind = &s[..i];
        let data = &s[i + 1 ..];

        match kind {
            "sha256" => {
                if data.len() != 64 {
                    return Err(de::Error::invalid_length(
                        data.len(),
                        &"sha256:DATA, where DATA is a 64-digit hex string",
                    ));
                }
                let mut hash = [0_u32; 8];
                for i in 0..8 {
                    let chunk = &data[i * 8 .. (i + 1) * 8];
                    hash[i] = u32::from_str_radix(chunk, 16).map_err(|_| {
                        de::Error::invalid_value(
                            de::Unexpected::Str(chunk),
                            &"hex digits",
                        )
                    })?;
                }
                Ok(Commitment::Sha256(hash))
            },

            _ => {
                return Err(de::Error::unknown_variant(
                    kind,
                    &["sha256"],
                ));
            },
        }
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
            "spontaneous_jump" => {
                seq.expect += 1;
                let dest = seq.next_element()?;
                SegmentConstraint::SpontaneousJump(dest)
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
                let tainted = is_mode::<AnyTainted>();
                if tainted {
                    seq.expect += 1;
                }
                Advice::MemOp {
                    addr: seq.next_element()?,
                    value: seq.next_element()?,
                    op: seq.next_element()?,
                    width: seq.next_element()?,
                    tainted: if tainted {seq.next_element()?} else {IfMode::none()},
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


impl<'de> Deserialize<'de> for TraceChunk {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_any(TraceChunkVisitor)
    }
}

struct TraceChunkVisitor;
impl<'de> Visitor<'de> for TraceChunkVisitor {
    type Value = TraceChunk;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a segment object")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<TraceChunk, A::Error> {
        let mut x = TraceChunk {
            segment: 0,
            states: Vec::new(),
            debug: None,
        };

        let mut seen = HashSet::new();
        while let Some(k) = map.next_key::<String>()? {
            if !seen.insert(k.clone()) {
                return Err(serde::de::Error::custom(format_args!(
                    "duplicate key {:?}", k,
                )));
            }

            match &k as &str {
                "segment" => { x.segment = map.next_value()?; },
                "states" => { x.states = map.next_value()?; },
                "debug" => { x.debug = Some(map.next_value()?); },
                _ => return Err(serde::de::Error::custom(format_args!(
                    "unknown key {:?}", k,
                ))),
            }
        }

        Ok(x)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, seq: A) -> Result<TraceChunk, A::Error> {
        let mut seq = CountedSeqAccess::new(seq, 2);
        let x = TraceChunk {
            segment: seq.next_element()?,
            states: seq.next_element()?,
            debug: None,
        };
        seq.finish()?;
        Ok(x)
    }
}



#[derive(Debug)]
enum AnyTrace {
    Flat(Vec<RamState>),
    /// MicroRAM outputs the trace as a list of pairs rather than a map with named keys.  Without
    /// the names, there's no distinction between the `Instr` and `Bbmd` formats when parsing.
    /// Thus, we parse into this generic form and convert to the more specific type later.
    Ambiguous(Vec<(usize, Vec<RamState>)>),
    Instr(Vec<TraceChunk>),
    Bbmd(Vec<BbmdTraceChunk>),
}

/// Manual `DeserializeImpl` for `AnyTrace`.  This does roughly the same thing as putting
/// `#[derive(Deserialize)] #[serde(untagged)]` on the declaration of `AnyTrace`, but provides
/// better error messages when all variants fail to parse.
impl<'de> Deserialize<'de> for AnyTrace {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let content = serde::__private::de::Content::deserialize(d)?;
        let deserializer = serde::__private::de::ContentRefDeserializer::new(&content);

        let err1: D::Error = match Deserialize::deserialize(deserializer) {
            Ok(x) => return Ok(AnyTrace::Flat(x)),
            Err(e) => e,
        };
        let err2: D::Error = match Deserialize::deserialize(deserializer) {
            Ok(x) => return Ok(AnyTrace::Ambiguous(x)),
            Err(e) => e,
        };
        let err3: D::Error = match Deserialize::deserialize(deserializer) {
            Ok(x) => return Ok(AnyTrace::Instr(x)),
            Err(e) => e,
        };
        let err4: D::Error = match Deserialize::deserialize(deserializer) {
            Ok(x) => return Ok(AnyTrace::Bbmd(x)),
            Err(e) => e,
        };
        Err(de::Error::custom(format_args!(
            "failed to parse as AnyTrace::Flat: {err1}; \
            failed to parse as AnyTrace::Ambiguous: {err2}; \
            failed to parse as AnyTrace::Instr: {err3}; \
            failed to parse as AnyTrace::Bbmd: {err4}")))
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
