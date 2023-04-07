use std::collections::HashMap;
use crate::micro_ram::types::{MultiExec, ExecBody, Segment, Advice};


#[derive(Clone, Debug)]
pub struct SegmentWitness {
    pub advice: Vec<u64>,
    pub stutter: Vec<bool>,

    /// Index of the previous segment in the trace, if any.
    pub pred: Option<usize>,
    /// Index of the next segment in the trace, if any.
    pub succ: Option<usize>,
    /// Whether the connection from the previous segment to the current one went through the
    /// routing network.
    pub from_net: bool,
    /// Whether the connection from this segment to the next one went through the routing network.
    pub to_net: bool,
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
        let mut prev_seg_idx: Option<usize> = None;
        for tc in &e.trace {
            let seg_idx = tc.segment;
            let seg = &e.segments[seg_idx];
            let seg_w = &mut w.segments[seg_idx];

            if let Some(ref debug) = tc.debug {
                if let Some(debug_cycle) = debug.cycle {
                    i = debug_cycle as u64;
                }
                if debug.clear_prev_segment {
                    prev_seg_idx = None;
                }
                if let Some(debug_prev) = debug.prev_segment {
                    prev_seg_idx = Some(debug_prev);
                }
            }

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

            if let Some(prev_seg_idx) = prev_seg_idx {
                let prev_seg = &e.segments[prev_seg_idx];
                let direct_connect = prev_seg.successors.contains(&seg_idx);
                seg_w.pred = Some(prev_seg_idx);
                seg_w.from_net = !direct_connect;

                let prev_seg_w = &mut w.segments[prev_seg_idx];
                prev_seg_w.succ = Some(seg_idx);
                prev_seg_w.to_net = !direct_connect;
            }

            prev_seg_idx = Some(seg_idx);
        }

        w
    }
}

impl SegmentWitness {
    pub fn default_from_raw(s: &Segment) -> SegmentWitness {
        SegmentWitness {
            advice: vec![0; s.len],
            stutter: vec![false; s.len],

            pred: None,
            succ: None,
            from_net: false,
            to_net: false,
        }
    }
}
