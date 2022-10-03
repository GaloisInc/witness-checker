use std::collections::{HashMap, BTreeMap};
use std::convert::TryFrom;
use std::ops::Index;
use crate::micro_ram::fetch::PADDING_INSTR;
use crate::micro_ram::trace::InstrLookup;
use crate::micro_ram::types::{
    MultiExec, ExecBody, Segment, Advice, RamInstr, RamState, MemPort, CodeSegment,
    MEM_PORT_UNUSED_CYCLE,
};


#[derive(Clone, Debug)]
pub struct SegmentWitness {
    pub init_state: RamState,
    pub fetches: Vec<(u64, RamInstr)>,
    pub mem_ports: Vec<Option<MemPort>>,

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
    /// Data values for initial memory segments.
    pub init_mem_values: Vec<Vec<u64>>,
    pub init_fetch_instrs: Vec<Vec<RamInstr>>,
}

#[derive(Clone, Debug)]
pub struct MultiExecWitness {
    pub execs: HashMap<String, ExecWitness>,
}


impl MultiExecWitness {
    pub fn from_raw(
        me: &MultiExec,
    ) -> MultiExecWitness {
        MultiExecWitness {
            execs: me.execs.iter().map(|(k, v)| {
                (k.clone(), ExecWitness::from_raw(v))
            }).collect(),
        }
    }
}

impl ExecWitness {
    pub fn from_raw(e: &ExecBody) -> ExecWitness {
        let default_init_state = RamState::default_with_regs(e.params.num_regs);
        let mut w = ExecWitness {
            segments: e.segments.iter().map(|s| {
                SegmentWitness::from_raw(s, default_init_state.clone())
            }).collect(),
            init_mem_values: e.init_mem.iter().map(|ms| {
                let mut data = ms.data.clone();
                assert!(data.len() <= ms.len as usize);
                data.resize(ms.len as usize, 0);
                data
            }).collect(),
            init_fetch_instrs: e.program.iter().map(|cs| {
                let mut instrs = cs.instrs.clone();
                assert!(instrs.len() <= cs.len as usize);
                instrs.resize(cs.len as usize, PADDING_INSTR);
                instrs
            }).collect(),
        };

        let instrs = InstrLookup::new(&e.program);

        let mut pc = 0;
        let mut cycle = 0;
        let mut prev_state = e.provided_init_state.clone().unwrap_or_else(|| e.initial_state());
        let mut prev_seg_idx: Option<usize> = None;
        for tc in &e.trace {
            let seg_idx = tc.segment;
            let seg = &e.segments[seg_idx];
            let seg_w = &mut w.segments[seg_idx];

            if let Some(ref debug) = tc.debug {
                if let Some(debug_cycle) = debug.cycle {
                    cycle = debug_cycle;
                }
                if let Some(ref debug_state) = debug.prev_state {
                    pc = debug_state.pc;
                    prev_state = debug_state.clone();
                }
                if debug.clear_prev_segment {
                    prev_seg_idx = None;
                }
                if let Some(debug_prev) = debug.prev_segment {
                    prev_seg_idx = Some(debug_prev);
                }
            }

            seg_w.init_state = RamState { cycle, live:true, .. prev_state };
            seg_w.fetches.reserve(seg.len);
            seg_w.mem_ports.resize(seg.len, None);

            debug_assert_eq!(seg.len, tc.states.len());
            for (j, post_state) in tc.states.iter().enumerate() {
                if let Some(advs) = e.advice.get(&(cycle as u64 + 1)) {
                    for adv in advs {
                        match *adv {
                            Advice::MemOp { addr, value, op, width, tainted } => {
                                seg_w.mem_ports[j] = Some(MemPort {
                                    cycle, addr, value, op, width, tainted
                                });
                            },
                            Advice::Stutter => { seg_w.stutter[j] = true; },
                            Advice::Advise { advise } => { seg_w.advice[j] = advise; },
                        }
                    }
                }

                seg_w.fetches.push((pc, instrs[pc]));

                pc = post_state.pc;
                cycle += 1;
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
            prev_state = tc.states.last().unwrap().clone();
        }

        w
    }
}

impl SegmentWitness {
    pub fn from_raw(s: &Segment, init_state: RamState) -> SegmentWitness {
        SegmentWitness {
            init_state,
            fetches: Vec::new(),
            mem_ports: Vec::new(),

            advice: vec![0; s.len],
            stutter: vec![false; s.len],

            pred: None,
            succ: None,
            from_net: false,
            to_net: false,
        }
    }

    pub fn live(&self) -> bool {
        self.init_state.live
    }
}
