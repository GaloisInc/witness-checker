use std::collections::HashMap;
use std::iter;
use std::mem;
use crate::ir::typed::{TWire, TSecretHandle, Builder, Repr};
use crate::micro_ram::context::Context;
use crate::micro_ram::routing::{Routing, RoutingBuilder, InputId, OutputId};
use crate::micro_ram::types::{self, RamState, Params};


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
enum StateSource {
    /// The initial state of the CPU.
    CpuInit,
    /// The final state of segment `.0`.
    Segment(usize),
    /// The state produced by routing network output `.0`.
    Network(OutputId),
    /// The output of cycle breaker `.0`.
    CycleBreak(usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
enum Liveness {
    /// Always live.
    Always,
    /// Live when the edge from segment `.0` to segment `.1` is live.
    Edge(usize, usize),
    /// Live when the from-network flag of segment `.0` is active.
    FromNetwork(usize),
    /// Live when the to-network flag of segment `.0` is active.
    ToNetwork(usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
struct Predecessor {
    src: StateSource,
    live: Liveness,
}

/// A `SegmentNode` computes an initial state from its predecessors, applies some unspecified
/// computation to it, and returns the result as its final state.  The computation of the final
/// state is handled externally.
#[derive(Default)]
struct SegmentNode<'a> {
    /// The predecessors of this segment.
    preds: Vec<Predecessor>,
    /// A cache for storing the initial state constructed from `preds`.
    init_state_cache: Option<TWire<'a, RamState>>,
    /// The final state, as provided via `set_final`.
    final_state: Option<TWire<'a, RamState>>,

    from_net: Option<OutputId>,
    to_net: Option<InputId>,
}

/// A `CycleBreakNode` logically computes an initial state from its predecessors and returns it
/// unmodified as its final state.  However, internally, the `CycleBreakNode` uses a `Secret` to
/// store the state, so that its output is always available even if its inputs are not available
/// yet.  This method of breaking cycles lets us produce an acyclic circuit from a possibly cyclic
/// segment graph.  (In fact, nearly all real-life segment graphs are cyclic, since the network is
/// treated as a single node and many segments have the network as both predecessor and successor.)
struct CycleBreakNode<'a> {
    preds: Vec<Predecessor>,
    secret: TSecretHandle<'a, RamState>,
}

struct NetworkInputNode {
    pred: Predecessor,
    segment_index: usize,
}

enum NetworkState<'a> {
    /// We haven't built the network yet.  Final states for segments with `to_net` set can be fed
    /// directly to the routing network as inputs.
    Before(RoutingBuilder<'a, RamState>),
    /// We have built the routing network.  
    After(Routing<'a, RamState>),
}

pub struct SegGraphBuilder<'a> {
    // Nodes in the segment graph
    segments: Vec<SegmentNode<'a>>,
    cycle_breaks: Vec<CycleBreakNode<'a>>,
    network_inputs: Vec<NetworkInputNode>,

    // Edge liveness flags
    edges: HashMap<(usize, usize), TSecretHandle<'a, bool>>,
    from_net: HashMap<usize, TSecretHandle<'a, bool>>,
    to_net: HashMap<usize, TSecretHandle<'a, bool>>,

    // The state of routing network construction.
    network: NetworkState<'a>,

    default_state: RamState,
    cpu_init_state: TWire<'a, RamState>,
}

impl<'a> SegGraphBuilder<'a> {
    pub fn new(
        b: &Builder<'a>,
        seg_defs: &[types::Segment],
        params: &Params,
        cpu_init_state: TWire<'a, RamState>,
    ) -> SegGraphBuilder<'a> {
        let mut sg = SegGraphBuilder {
            segments: iter::repeat_with(SegmentNode::default).take(seg_defs.len()).collect(),
            cycle_breaks: Vec::new(),
            network_inputs: Vec::new(),

            edges: HashMap::new(),
            from_net: HashMap::new(),
            to_net: HashMap::new(),

            network: NetworkState::Before(RoutingBuilder::new()),

            default_state: RamState::default_with_regs(params.num_regs),
            cpu_init_state,
        };

        let network = match sg.network {
            NetworkState::Before(ref mut x) => x,
            _ => unreachable!(),
        };

        for (i, seg_def) in seg_defs.iter().enumerate() {
            if i == 0 {
                sg.segments[i].preds.push(Predecessor {
                    src: StateSource::CpuInit,
                    live: Liveness::Always,
                });
            }

            for &j in &seg_def.successors {
                assert!(!sg.edges.contains_key(&(i, j)), "duplicate edge {} -> {}", i, j);
                sg.edges.insert((i, j), b.secret().1);

                sg.segments[j].preds.push(Predecessor {
                    src: StateSource::Segment(i),
                    live: Liveness::Edge(i, j),
                });
            }

            if seg_def.enter_from_network {
                assert!(!sg.from_net.contains_key(&i), "duplicate edge net -> {}", i);
                sg.from_net.insert(i, b.secret().1);
                let output_id = network.add_output();
                sg.segments[i].preds.push(Predecessor {
                    src: StateSource::Network(output_id),
                    live: Liveness::FromNetwork(i),
                });
                sg.segments[i].from_net = Some(output_id);
            }

            if seg_def.exit_to_network {
                assert!(!sg.to_net.contains_key(&i), "duplicate edge {} -> net", i);
                sg.to_net.insert(i, b.secret().1);
                sg.network_inputs.push(NetworkInputNode {
                    pred: Predecessor {
                        src: StateSource::Segment(i),
                        live: Liveness::ToNetwork(i),
                    },
                    segment_index: i,
                });
            }
        }

        sg.break_cycles(b, params);

        sg
    }

    /// Break cycles in the graph by inserting `CycleBreakNodes`.
    fn break_cycles(&mut self, b: &Builder<'a>, params: &Params) {
        // For now, just insert a cycle-breaker before each segment.  This is very inefficient, but
        // is definitely correct.
        for (i, seg) in self.segments.iter_mut().enumerate() {
            let preds = mem::take(&mut seg.preds);
            let j = self.cycle_breaks.len();
            self.cycle_breaks.push(CycleBreakNode {
                preds,
                secret: RamState::secret(b, params.num_regs).1,
            });
            seg.preds.push(Predecessor {
                src: StateSource::CycleBreak(j),
                live: Liveness::Always,
            });
        }
    }

    /// Get the order in which to construct the segment circuits.  This ordering is guaranteed to
    /// respect dependencies between the segments.  Specifically, calling `get_initial` on element
    /// `k` of the ordering is guaranteed to succeed if `set_final` has been called on all elements
    /// prior to `k`.
    pub fn get_order(&self) -> impl Iterator<Item = SegGraphItem> {
        (0 .. self.segments.len()).map(SegGraphItem::Segment)
            .chain(iter::once(SegGraphItem::Network))
    }

    /// Obtain the initial state to use for a given segment.
    pub fn get_initial(&mut self, b: &Builder<'a>, idx: usize) -> &TWire<'a, RamState> {
        if self.segments[idx].init_state_cache.is_none() {
            let mut it = self.segments[idx].preds.iter();
            let first_pred = it.next()
                .unwrap_or_else(|| panic!("segment {} has no predecessors", idx));
            let mut first = self.get_final(first_pred.src).clone();
            // FIXME: copy liveness_flag(first_pred.live) into first.live
            // (current code can produce a live result even when no input edges are live)
            let state = it.fold(first, |acc, pred| {
                let live = self.liveness_flag(b, pred.live);
                b.mux(live, self.get_final(pred.src).clone(), acc)
            });
            self.segments[idx].init_state_cache = Some(state);
        }
        self.segments[idx].init_state_cache.as_ref().unwrap()
    }

    /// Set the final state for a given segment, which may be needed to compute the initial state
    /// for later segments.
    pub fn set_final(&mut self, idx: usize, state: TWire<'a, RamState>) {
        assert!(self.segments[idx].final_state.is_none(),
            "already set final state for segment {}", idx);
        self.segments[idx].final_state = Some(state);
    }

    fn get_final(&self, src: StateSource) -> &TWire<'a, RamState> {
        match src {
            StateSource::CpuInit => &self.cpu_init_state,
            StateSource::Segment(idx) =>
                self.segments[idx].final_state.as_ref()
                    .unwrap_or_else(|| panic!("{:?} final state is not initialized", src)),
            StateSource::Network(id) => match self.network {
                NetworkState::Before(_) =>
                    panic!("tried to access {:?} before building network", id),
                NetworkState::After(ref net) => &net[id],
            },
            StateSource::CycleBreak(idx) =>
                self.cycle_breaks[idx].secret.wire(),
        }
    }

    pub fn build_network(&mut self, b: &Builder<'a>) {
        let mut routing = match self.network {
            NetworkState::Before(ref mut rb) => mem::take(rb),
            NetworkState::After(_) => panic!("already built the routing network"),
        };

        for inp in &self.network_inputs {
            let mut state = self.get_final(inp.pred.src).clone();
            // FIXME: adjust state liveness (set to `to_net[inp.segment_index]`)
            // (current code can produce a live result even when the input edge is not live)
            let id = routing.add_input(state);
            assert!(self.segments[inp.segment_index].to_net.is_none(),
                "impossible: multiple to-net for segment {}?", inp.segment_index);
            self.segments[inp.segment_index].to_net = Some(id);
        }

        let default = self.default_state.clone();
        self.network = NetworkState::After(routing.finish_with_default(b, default));
    }

    fn liveness_flag(&self, b: &Builder<'a>, l: Liveness) -> TWire<'a, bool> {
        match l {
            Liveness::Always => b.lit(true),
            Liveness::Edge(a, b) => self.edges[&(a, b)].wire().clone(),
            Liveness::FromNetwork(i) => self.from_net[&i].wire().clone(),
            Liveness::ToNetwork(i) => self.to_net[&i].wire().clone(),
        }
    }

    pub fn finish(mut self, cx: &Context<'a>, b: &Builder<'a>) -> SegGraph<'a> {
        // Add equality assertions to constrain the CycleBreakNode secrets.  We do this first
        // because the later steps involve dismantling `self` to extract its `TSecretHandle`s.
        for (i, cbn) in self.cycle_breaks.iter().enumerate() {
            for &pred in &cbn.preds {
                let live = self.liveness_flag(b, pred.live);
                let state = self.get_final(pred.src);
                cx.when(b, live, |cx| {
                    wire_assert!(
                        cx, b.eq(cbn.secret.wire().clone(), state.clone()),
                        "CycleBreak {} incoming edge {:?} is live, but state doesn't match {:?}",
                        i, pred.live, pred.src,
                    );
                });
            }
        }


        let mut sg = SegGraph {
            segs: Vec::with_capacity(self.segments.len()),
            edges: self.edges,
            network: match self.network {
                NetworkState::Before(_) => panic!("must call build_network() before finish()"),
                NetworkState::After(net) => net,
            },
        };

        // Each `CycleBreakNode`'s `TSecretHandle` must be attached as either the `init_secret` or
        // `final_secret` of some segment.  Specifically, for a given `CycleBreakNode`, if its only
        // predecessor is a segment, then it can be that segment's `final_secret`, and if its only
        // successor is a segment, then it can be that segment's `init_secret`.  The requirement
        // satisfied in both cases is that the `CycleBreakNode` is live exactly when the segment is
        // live.
        //
        // We process final secrets first, then leave the remaining `CycleBreakNode`s to be claimed
        // by `SegInfo`s in the loop below.
        let mut final_secrets = HashMap::with_capacity(self.cycle_breaks.len());
        let mut remaining_cycle_breaks = HashMap::with_capacity(self.cycle_breaks.len());
        for (i, cbn) in self.cycle_breaks.into_iter().enumerate() {
            if cbn.preds.len() == 1 {
                if let StateSource::Segment(seg_idx) = cbn.preds[0].src {
                    final_secrets.insert(seg_idx, cbn.secret);
                    continue;
                }
            }
            remaining_cycle_breaks.insert(i, cbn);
        }

        let mut from_net_edges = self.from_net;
        let mut to_net_edges = self.to_net;
        for (idx, sn) in self.segments.into_iter().enumerate() {
            let mut seg = SegInfo::default();

            seg.from_net = sn.from_net.map(|id| {
                let live = from_net_edges.remove(&idx).unwrap_or_else(|| panic!(
                    "impossible: missing liveness flag for segment {} from_net", idx,
                ));
                (id, live)
            });

            seg.to_net = sn.to_net.map(|id| {
                let live = to_net_edges.remove(&idx).unwrap_or_else(|| panic!(
                    "impossible: missing liveness flag for segment {} to_net", idx,
                ));
                (id, live)
            });

            if sn.preds.len() == 1 {
                if let StateSource::CycleBreak(j) = sn.preds[0].src {
                    if let Some(cbn) = remaining_cycle_breaks.remove(&j) {
                        seg.init_secret = Some(cbn.secret);
                    }
                }
            }

            seg.final_secret = final_secrets.remove(&idx);

            sg.segs.push(seg);
        }

        // `segments` was consumed above.
        assert!(remaining_cycle_breaks.len() == 0,
            "found {} unconnected cycle breaks: {:?}",
            remaining_cycle_breaks.len(), remaining_cycle_breaks.keys().collect::<Vec<_>>());
        // `network_inputs` is no longer needed after `build_network()`.
        // `edges` was consumed above.
        assert!(from_net_edges.len() == 0,
            "found {} unused from_net edges: {:?}",
            from_net_edges.len(), from_net_edges.keys().collect::<Vec<_>>());
        assert!(to_net_edges.len() == 0,
            "found {} unused to_net edges: {:?}",
            to_net_edges.len(), to_net_edges.keys().collect::<Vec<_>>());
        // `network` was consumed above.

        sg
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SegGraphItem {
    Segment(usize),
    Network,
}


#[derive(Default)]
struct SegInfo<'a> {
    init_secret: Option<TSecretHandle<'a, RamState>>,
    final_secret: Option<TSecretHandle<'a, RamState>>,
    from_net: Option<(OutputId, TSecretHandle<'a, bool>)>,
    to_net: Option<(InputId, TSecretHandle<'a, bool>)>,
}

pub struct SegGraph<'a> {
    segs: Vec<SegInfo<'a>>,
    edges: HashMap<(usize, usize), TSecretHandle<'a, bool>>,
    network: Routing<'a, RamState>,
}

impl<'a> SegGraph<'a> {
    pub fn set_initial_secret(&self, b: &Builder<'a>, idx: usize, state: &RamState) {
        if let Some(ref s) = self.segs[idx].init_secret {
            s.set(b, state.clone());
        }
    }

    pub fn set_final_secret(&self, b: &Builder<'a>, idx: usize, state: &RamState) {
        if let Some(ref s) = self.segs[idx].final_secret {
            s.set(b, state.clone());
        }
    }

    pub fn make_edge_live(&mut self, b: &Builder<'a>, src: usize, dest: usize) {
        if let Some(ref live) = self.edges.get(&(src, dest)) {
            // Easy case: a direct edge between `src` and `dest`.
            live.set(b, true);
            return;
        }

        // There is no direct edge, so this connection must go through the routing network.
        let &(inp, ref inp_secret) = self.segs[src].to_net.as_ref()
            .unwrap_or_else(|| panic!("no outgoing edge from {} to {}", src, dest));
        let &(out, ref out_secret) = self.segs[dest].from_net.as_ref()
            .unwrap_or_else(|| panic!("no incoming edge from {} to {}", src, dest));
        self.network.connect(inp, out);
        inp_secret.set(b, true);
        out_secret.set(b, true);
    }

    pub fn finish(self, b: &Builder<'a>) {
        self.network.finish(b);
    }
}
