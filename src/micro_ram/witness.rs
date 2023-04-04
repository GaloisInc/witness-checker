use std::collections::HashMap;
use crate::micro_ram::types::{MultiExec, ExecBody, Segment, Advice};


#[derive(Clone, Debug)]
pub struct SegmentWitness {
    pub advice: Vec<u64>,
    pub stutter: Vec<bool>,
}

#[derive(Clone, Debug)]
pub struct ExecWitness {
    pub segments: Vec<SegmentWitness>,
}

#[derive(Clone, Debug)]
pub struct MultiExecWitness {
    pub execs: HashMap<String, ExecWitness>,
}


impl MultiExecWitness {
    pub fn from_raw(me: &MultiExec) -> MultiExecWitness {
        MultiExecWitness {
            execs: me.execs.iter().map(|(k, v)| {
                (k.clone(), ExecWitness::from_raw(v))
            }).collect(),
        }
    }
}

impl ExecWitness {
    pub fn from_raw(e: &ExecBody) -> ExecWitness {
        let mut w = ExecWitness {
            segments: e.segments.iter().map(|s| SegmentWitness::default_from_raw(s)).collect(),
        };

        let mut i = 0;
        for tc in &e.trace {
            let seg = &e.segments[tc.segment];
            let seg_w = &mut w.segments[tc.segment];
            for j in 0 .. seg.len {
                if let Some(advs) = e.advice.get(&(i + 1)) {
                    for adv in advs {
                        match *adv {
                            Advice::MemOp { .. } => {},
                            Advice::Stutter => { seg_w.stutter[j] = true; },
                            Advice::Advise { advise } => { seg_w.advice[j] = advise; },
                        }
                    }
                }
                i += 1;
            }
        }

        w
    }
}

impl SegmentWitness {
    pub fn default_from_raw(s: &Segment) -> SegmentWitness {
        SegmentWitness {
            advice: vec![0; s.len],
            stutter: vec![false; s.len],
        }
    }
}
