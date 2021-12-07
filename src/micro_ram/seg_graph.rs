use std::collections::HashMap;
use std::iter;
use std::mem;
use crate::ir::typed::{TWire, TSecretHandle, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{self, RamState, Params};
use crate::routing::{Routing, RoutingBuilder, InputId, OutputId};


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
    cpu_init_state: RamState,
    cpu_init_state_wire: TWire<'a, RamState>,
}

impl<'a> SegGraphBuilder<'a> {
    pub fn new(
        b: &Builder<'a>,
        seg_defs: &[types::Segment],
        params: &Params,
        cpu_init_state: RamState,
    ) -> SegGraphBuilder<'a> {
        let _g = b.scoped_label("seg_graph");
        let mut sg = SegGraphBuilder {
            segments: iter::repeat_with(SegmentNode::default).take(seg_defs.len()).collect(),
            cycle_breaks: Vec::new(),
            network_inputs: Vec::new(),

            edges: HashMap::new(),
            from_net: HashMap::new(),
            to_net: HashMap::new(),

            network: NetworkState::Before(RoutingBuilder::new()),

            default_state: RamState::default_with_regs(params.num_regs),
            cpu_init_state: cpu_init_state.clone(),
            cpu_init_state_wire: b.lit(cpu_init_state),
        };

        let network = match sg.network {
            NetworkState::Before(ref mut x) => x,
            _ => unreachable!(),
        };

        for (i, seg_def) in seg_defs.iter().enumerate() {
            let _g = b.scoped_label(format_args!("segment/{}", i));
            if i == 0 {
                sg.segments[i].preds.push(Predecessor {
                    src: StateSource::CpuInit,
                    live: Liveness::Always,
                });
            }

            for &j in &seg_def.successors {
                let _g = b.scoped_label(format_args!("successor {}", j));
                assert!(!sg.edges.contains_key(&(i, j)), "duplicate edge {} -> {}", i, j);
                sg.edges.insert((i, j), b.secret().1);

                sg.segments[j].preds.push(Predecessor {
                    src: StateSource::Segment(i),
                    live: Liveness::Edge(i, j),
                });
            }

            if seg_def.enter_from_network {
                let _g = b.scoped_label("from net");
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
                let _g = b.scoped_label("to net");
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
            let _g = b.scoped_label(format_args!("cycle break {}", i));
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
        let _g = b.scoped_label(format_args!("seg_graph/get_initial/{}", idx));
        if self.segments[idx].init_state_cache.is_none() {
            let mut it = self.segments[idx].preds.iter();
            let first_pred = it.next()
                .unwrap_or_else(|| panic!("segment {} has no predecessors", idx));
            let first = self.get_predecessor(b, *first_pred);
            let state = it.fold(first, |acc, pred| {
                let state = self.get_predecessor(b, *pred);
                b.mux(state.live, state, acc)
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
            StateSource::CpuInit => &self.cpu_init_state_wire,
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

    fn liveness_flag(&self, b: &Builder<'a>, l: Liveness) -> TWire<'a, bool> {
        match l {
            Liveness::Always => b.lit(true),
            Liveness::Edge(a, b) => self.edges[&(a, b)].wire().clone(),
            Liveness::FromNetwork(i) => self.from_net[&i].wire().clone(),
            Liveness::ToNetwork(i) => self.to_net[&i].wire().clone(),
        }
    }

    fn get_predecessor(&self, b: &Builder<'a>, pred: Predecessor) -> TWire<'a, RamState> {
        let mut wire = self.get_final(pred.src).clone();
        let edge_live = self.liveness_flag(b, pred.live);
        wire.live = b.and(wire.live, edge_live);
        wire
    }

    pub fn build_network(&mut self, b: &Builder<'a>) {
        let _g = b.scoped_label("seg_graph/build_network");
        let mut routing = match self.network {
            NetworkState::Before(ref mut rb) => mem::take(rb),
            NetworkState::After(_) => panic!("already built the routing network"),
        };

        for inp in &self.network_inputs {
            let mut state = self.get_final(inp.pred.src).clone();
            // Force `state.live` to `false` if the edge leading to this network port is not live.
            // Note the edge can't be live unless the source segment is live (this is asserted in
            // `finish`).
            state.live = *self.to_net[&inp.segment_index].wire();
            let id = routing.add_input(state);
            assert!(self.segments[inp.segment_index].to_net.is_none(),
                "impossible: multiple to-net for segment {}?", inp.segment_index);
            self.segments[inp.segment_index].to_net = Some(id);
        }

        let default = self.default_state.clone();
        self.network = NetworkState::After(routing.finish_with_default(b, default));
    }

    pub fn finish(self, cx: &Context<'a>, b: &Builder<'a>) -> SegGraph<'a> {
        let _g = b.scoped_label("seg_graph/finish");
        // Add equality assertions to constrain the CycleBreakNode secrets.  We do this first
        // because the later steps involve dismantling `self` to extract its `TSecretHandle`s.
        for (i, cbn) in self.cycle_breaks.iter().enumerate() {
            let mut count = b.lit(0_u8);
            assert!(cbn.preds.len() <= u8::MAX as usize);
            for &pred in &cbn.preds {
                let state = self.get_predecessor(b, pred);
                count = b.add(count, b.cast(state.live));
                cx.when(b, state.live, |cx| {
                    wire_assert!(
                        cx, b.eq(cbn.secret.wire().clone(), state),
                        "CycleBreak {} incoming edge {:?} is live, but state doesn't match {:?}",
                        i, pred.live, pred.src,
                    );
                });
            }

            // If the CycleBreakNode's secret state is live, then at least one input must be live.
            cx.when(b, cbn.secret.wire().live, |cx| {
                wire_assert!(
                    cx, b.ne(count, b.lit(0)),
                    "CycleBreak {} has live output but no live inputs",
                    i,
                );
            });
        }

        // Assert that at most one outgoing edge is live from each live segment.  This prevents the
        // prover from cheating by "spawning" a second execution that modifies memory concurrently
        // with the main execution.
        //
        // Also assert that no outgoing edges are live from non-live segments.  This prevents the
        // prover from spawning a second execution from nowhere with no connection to the initial
        // state.
        //
        // We don't need a similar check for incoming edges because the initial state of the
        // segment can only be equal to one predecessor's final state.  Any other live predecessors
        // will have their states ignored, so they effectively die on entry to the segment.
        let mut edge_list = self.edges.keys().cloned().collect::<Vec<_>>();
        edge_list.sort();
        let mut start = 0;
        for i in 0 .. self.segments.len() {
            // Consume a block of `(i, j)` pairs that all have the same `i` value.
            let end = edge_list[start..].iter().position(|&(ii, _)| ii != i).map(|x| x + start)
                .unwrap_or(edge_list.len());
            debug_assert!(edge_list[start..end].iter().all(|&(ii, _)| ii == i));

            let mut wires = Vec::with_capacity(end - start + 1);
            for &(_, j) in &edge_list[start..end] {
                wires.push(*self.edges[&(i, j)].wire());
            }
            if let Some(to_net_live) = self.to_net.get(&i) {
                wires.push(*to_net_live.wire());
            }
            assert!(wires.len() <= u8::MAX as usize);

            let segment_live = self.segments[i].final_state.as_ref()
                .unwrap_or_else(|| panic!("missing final state for segment {}", i))
                .live;
            // Check that the number of live outgoing edges is within the appropriate bounds,
            // depending on `segment_live`.  The `count` is also produced for debugging purposes.
            let (ok, count) = match wires.len() {
                0 => (b.lit(true), b.lit(0)),
                1 => {
                    (b.or(segment_live, b.not(wires[0])), b.cast(wires[0]))
                },
                _ => {
                    let count = wires.into_iter()
                        .fold(b.lit(0), |acc, w| b.add(acc, b.cast(w)));
                    (
                        b.or(
                            b.eq(count, b.lit(0)),
                            b.and(segment_live, b.eq(count, b.lit(1))),
                        ),
                        count,
                    )
                },
            };

            wire_assert!(
                cx, ok,
                "segment {} ({}) has {} live successors (expected 0{})",
                i, cx.eval(segment_live).map(|b| if b { "live" } else { "dead" }),
                cx.eval(count), if cx.eval(segment_live).0 != Some(false) { " or 1" } else { "" },
            );

            start = end;
        }
        assert_eq!(start, edge_list.len());


        // Find which CycleBreakNode (if any) is present on each edge.
        let mut edge_cbns = HashMap::new();
        let mut from_net_cbns = HashMap::new();
        let mut to_net_cbns = HashMap::new();

        // Look for {CpuInit,Segment,Network} -> CycleBreak -> Segment
        for (j, seg) in self.segments.iter().enumerate() {
            for seg_pred in &seg.preds {
                let cbn = match seg_pred.src {
                    StateSource::CycleBreak(x) => x,
                    _ => continue,
                };
                for cbn_pred in &self.cycle_breaks[cbn].preds {
                    match cbn_pred.src {
                        StateSource::CpuInit => {},
                        StateSource::Segment(i) => {
                            assert!(!edge_cbns.contains_key(&(i, j)),
                                "multiple edges from {} to {}", i, j);
                            edge_cbns.insert((i, j), cbn);
                        },
                        StateSource::Network(_) => {
                            assert!(!from_net_cbns.contains_key(&j),
                                "multiple edges from net to {}", j);
                            from_net_cbns.insert(j, cbn);
                        },
                        StateSource::CycleBreak(cbn2) => {
                            panic!("CycleBreak {} connects directly to CycleBreak {}",
                                cbn, cbn2);
                        },
                    }
                }
            }
        }

        // Look for Segment -> CycleBreak -> Network
        for net in self.network_inputs.iter() {
            let cbn = match net.pred.src {
                StateSource::CycleBreak(x) => x,
                _ => continue,
            };
            for cbn_pred in &self.cycle_breaks[cbn].preds {
                match cbn_pred.src {
                    StateSource::CpuInit => {
                        panic!("CpuInit connects to Network via CycleBreak {}", cbn);
                    },
                    StateSource::Segment(i) => {
                        assert!(!to_net_cbns.contains_key(&i),
                            "multiple edges from {} to net", i);
                        to_net_cbns.insert(i, cbn);
                    },
                    StateSource::Network(_) => {
                        panic!("Network connects to Network via CycleBreak {}", cbn);
                    },
                    StateSource::CycleBreak(cbn2) => {
                        panic!("CycleBreak {} connects directly to CycleBreak {}",
                            cbn, cbn2);
                    },
                }
            }
        }


        // Special handling for CpuInit.

        // Sanity check: there should be exactly one incoming edge from CpuInit.
        let cpu_init_count = self.segments.iter().flat_map(|n| n.preds.iter())
            .chain(self.cycle_breaks.iter().flat_map(|n| n.preds.iter()))
            .filter(|p| p.src == StateSource::CpuInit).count();
        assert_eq!(cpu_init_count, 1);

        // The edge from CpuInit is always live.  If that edge passes through a CycleBreakNode, we
        // set the secret for that node.
        for cbn in self.cycle_breaks.iter() {
            if cbn.preds.iter().any(|p| p.src == StateSource::CpuInit) {
                cbn.secret.set(b, self.cpu_init_state.clone());
            }
        }


        // Build the final SegGraph

        let mut sg = SegGraph {
            segs: Vec::with_capacity(self.segments.len()),
            edges: self.edges.into_iter().map(|(k, live)| {
                let state_index = edge_cbns.remove(&k);
                (k, EdgeSecrets { live, state_index })
            }).collect(),
            edge_states: self.cycle_breaks.into_iter().map(|cbn| cbn.secret).collect(),
            network: match self.network {
                NetworkState::Before(_) => panic!("must call build_network() before finish()"),
                NetworkState::After(net) => net,
            },
        };

        let mut from_net_edges = self.from_net;
        let mut to_net_edges = self.to_net;
        for (idx, sn) in self.segments.into_iter().enumerate() {
            let mut seg = SegInfo::default();

            seg.from_net = sn.from_net.map(|id| {
                let live = from_net_edges.remove(&idx).unwrap_or_else(|| panic!(
                    "impossible: missing liveness flag for segment {} from_net", idx,
                ));
                let state_index = from_net_cbns.remove(&idx);
                (id, EdgeSecrets { live, state_index })
            });

            seg.to_net = sn.to_net.map(|id| {
                let live = to_net_edges.remove(&idx).unwrap_or_else(|| panic!(
                    "impossible: missing liveness flag for segment {} to_net", idx,
                ));
                let state_index = from_net_cbns.remove(&idx);
                (id, EdgeSecrets { live, state_index })
            });

            sg.segs.push(seg);
        }

        // `segments` was consumed above.
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


struct EdgeSecrets<'a> {
    live: TSecretHandle<'a, bool>,
    state_index: Option<usize>,
}

#[derive(Default)]
struct SegInfo<'a> {
    from_net: Option<(OutputId, EdgeSecrets<'a>)>,
    to_net: Option<(InputId, EdgeSecrets<'a>)>,
}

pub struct SegGraph<'a> {
    segs: Vec<SegInfo<'a>>,
    edges: HashMap<(usize, usize), EdgeSecrets<'a>>,
    edge_states: Vec<TSecretHandle<'a, RamState>>,
    network: Routing<'a, RamState>,
}

impl<'a> SegGraph<'a> {
    fn make_edge_live_inner(
        edge_states: &mut [TSecretHandle<'a, RamState>],
        edge: &EdgeSecrets<'a>,
        b: &Builder<'a>,
        state: &RamState,
    ) {
        edge.live.set(b, true);
        if let Some(idx) = edge.state_index {
            edge_states[idx].set(b, state.clone());
        }
    }

    pub fn make_edge_live(&mut self, b: &Builder<'a>, src: usize, dest: usize, state: &RamState) {
        if let Some(ref edge) = self.edges.get(&(src, dest)) {
            // Easy case: a direct edge between `src` and `dest`.
            Self::make_edge_live_inner(&mut self.edge_states, edge, b, state);
            return;
        }

        // There is no direct edge, so this connection must go through the routing network.
        let &(inp, ref inp_edge) = self.segs[src].to_net.as_ref()
            .unwrap_or_else(|| panic!("no outgoing edge from {} to {}", src, dest));
        let &(out, ref out_edge) = self.segs[dest].from_net.as_ref()
            .unwrap_or_else(|| panic!("no incoming edge from {} to {}", src, dest));
        self.network.connect(inp, out);
        Self::make_edge_live_inner(&mut self.edge_states, inp_edge, b, state);
        Self::make_edge_live_inner(&mut self.edge_states, out_edge, b, state);
    }

    pub fn finish(self, b: &Builder<'a>) {
        self.network.finish(b);
    }
}
