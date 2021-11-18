use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::iter;
use std::mem;
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{TWire, TSecretHandle, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::types::{self, RamState, Params, TraceChunk};
use crate::routing::{RoutingBuilder, InputId, OutputId};


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
struct Predecessor {
    src: StateSource,
    live: Liveness,
}

/// A `SegmentNode` computes an initial state from its predecessors, applies some unspecified
/// computation to it, and returns the result as its final state.  The computation of the final
/// state is handled externally.
#[derive(Default, Migrate)]
struct SegmentNode<'a> {
    /// The predecessors of this segment.
    preds: Vec<Predecessor>,
    /// The final state, as provided via `set_final`.
    final_state: Option<TWire<'a, RamState>>,

    from_net: Option<OutputId>,
    to_net: Option<InputId>,

    /// Tracks whether `take_initial_mem` has been called on this segment.
    took_initial_mem: bool,
    final_mem: Counted<KnownMem<'a>>,
}

/// A `CycleBreakNode` logically computes an initial state from its predecessors and returns it
/// unmodified as its final state.  However, internally, the `CycleBreakNode` uses a `Secret` to
/// store the state, so that its output is always available even if its inputs are not available
/// yet.  This method of breaking cycles lets us produce an acyclic circuit from a possibly cyclic
/// segment graph.  (In fact, nearly all real-life segment graphs are cyclic, since the network is
/// treated as a single node and many segments have the network as both predecessor and successor.)
#[derive(Migrate)]
struct CycleBreakNode<'a> {
    preds: Vec<Predecessor>,
    secret: TSecretHandle<'a, RamState>,
}

#[derive(Migrate)]
struct NetworkInputNode {
    pred: Predecessor,
    segment_index: usize,
}

#[derive(Migrate)]
enum NetworkState<'a> {
    /// We haven't built the network yet.  Final states for segments with `to_net` set can be fed
    /// directly to the routing network as inputs.
    Before(RoutingBuilder<'a, RamState>),
    /// We have built the routing network.  
    After(Vec<TWire<'a, RamState>>),
}

#[derive(Migrate)]
pub struct SegGraphBuilder<'a> {
    // Nodes in the segment graph
    segments: Vec<SegmentNode<'a>>,
    cycle_breaks: Vec<CycleBreakNode<'a>>,
    network_inputs: Vec<NetworkInputNode>,

    // Edge liveness flags
    edges: HashMap<(usize, usize), TSecretHandle<'a, bool>>,
    from_net: HashMap<usize, TSecretHandle<'a, bool>>,
    to_net: HashMap<usize, TSecretHandle<'a, bool>>,

    /// The state of routing network construction.
    network: NetworkState<'a>,
    /// Paths that must be connected once the routing network has been constructed.
    network_conns: Vec<(usize, usize)>,

    default_state: RamState,
    cpu_init_state: RamState,
    cpu_init_state_wire: TWire<'a, RamState>,
    cpu_init_mem: Counted<KnownMem<'a>>,

    panic_on_drop: PanicOnDrop,
}

impl<'a> SegGraphBuilder<'a> {
    pub fn new(
        b: &Builder<'a>,
        seg_defs: &[types::Segment],
        params: &Params,
        cpu_init_state: RamState,
        trace: &[TraceChunk],
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
            network_conns: Vec::new(),

            default_state: RamState::default_with_regs(params.num_regs),
            cpu_init_state: cpu_init_state.clone(),
            cpu_init_state_wire: b.lit(cpu_init_state),
            cpu_init_mem: Counted::new(),

            panic_on_drop: PanicOnDrop::new(),
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
                // Note that `enter_from_network` is ignored for segment 0.
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
                // Note we don't set `sg.segments[i].to_net`, since `routing.add_input` requires a
                // wire for the input to the routing network.  Instead, the `to_net` field is set
                // during `build_network()`.
            }
        }

        sg.break_cycles(b, params);
        sg.mark_unreachable();
        sg.count_final_mem_users();

        sg.init_secrets(b, trace);

        sg
    }

    pub fn dump(&self) -> String {
        let mut s = String::new();

        macro_rules! source_node {
            ($src:expr) => {
                match $src {
                    StateSource::CpuInit => "init".to_string(),
                    StateSource::Segment(j) => format!("seg{}", j),
                    StateSource::Network(out_id) => {
                        writeln!(s, r#"net_out{} [ label = "*" ];"#, out_id.into_raw()).unwrap();
                        format!("net_out{}", out_id.into_raw())
                    },
                    StateSource::CycleBreak(j) => format!("cb{}", j),
                }
            };
        }

        writeln!(s, "digraph {{").unwrap();
        writeln!(s, "init;").unwrap();

        for (i, seg) in self.segments.iter().enumerate() {
            writeln!(s, r#"seg{} [ label="seg{}" ];"#, i, i).unwrap();
            for pred in &seg.preds {
                let pred_node = source_node!(pred.src);
                writeln!(s, "{} -> seg{};", pred_node, i).unwrap();
            }
        }

        for (i, cb) in self.cycle_breaks.iter().enumerate() {
            writeln!(s, r#"cb{} [ label="cb{}" ];"#, i, i).unwrap();
            for pred in &cb.preds {
                let pred_node = source_node!(pred.src);
                writeln!(s, "{} -> cb{};", pred_node, i).unwrap();
            }
        }

        for (i, net) in self.network_inputs.iter().enumerate() {
            writeln!(s, r#"net_in{} [ label="*" ];"#, i).unwrap();
            let pred_node = source_node!(net.pred.src);
            writeln!(s, "{} -> net_in{};", pred_node, i).unwrap();
        }

        writeln!(s, "}}").unwrap();

        s
    }

    /// Break cycles in the graph by inserting `CycleBreakNodes`.
    fn break_cycles(&mut self, b: &Builder<'a>, params: &Params) {
        // If a segment's `good` flag is set, then there are no cycles involving that node or any
        // of its (transitive) predecessors.
        let mut good = vec![false; self.segments.len()];

        enum Step {
            Enter(usize),
            Exit(usize),
        }

        let mut visited = HashSet::new();
        let mut stack = Vec::new();

        for i in 0 .. self.segments.len() {
            if good[i] {
                continue;
            }

            stack.push(Step::Enter(i));

            while let Some(step) = stack.pop() {
                let i = match step {
                    Step::Enter(i) => i,
                    Step::Exit(i) => {
                        visited.remove(&i);
                        good[i] = true;
                        continue;
                    },
                };
                if good[i] {
                    continue;
                }

                debug_assert!(!visited.contains(&i));
                visited.insert(i);
                // Push `Exit(i)` first so that it happens last, after all outgoing edges have been
                // processed.
                stack.push(Step::Exit(i));

                let seg = &mut self.segments[i];
                let num_preds = seg.preds.len();
                for pred in &mut seg.preds {
                    match pred.src {
                        StateSource::Segment(j) => {
                            if good[j] {
                                continue;
                            }
                            if !visited.contains(&j) {
                                stack.push(Step::Enter(j));
                                continue;
                            }
                            // Otherwise, the edge from `i` to `j` is a back edge, so insert a
                            // cycle break for it.
                        },
                        // Always insert a cycle break on edges from network.
                        StateSource::Network(_) => {},
                        _ => continue,
                    }

                    let cb_idx = self.cycle_breaks.len();
                    self.cycle_breaks.push(CycleBreakNode {
                        preds: vec![*pred],
                        secret: RamState::secret(b, params.num_regs).1,
                    });
                    *pred = Predecessor {
                        src: StateSource::CycleBreak(cb_idx),
                        live: if num_preds == 1 { Liveness::Always } else { pred.live },
                    };
                }
            }

            debug_assert!(stack.len() == 0);
            debug_assert!(visited.len() == 0);
        }
    }

    /// Mark all nodes that are unreachable from the init state and the network.  Nodes are marked
    /// by clearing their predecessor list, making them obviously unreachable.
    fn mark_unreachable(&mut self) {
        // If a node's "dead" flag is set, the node is unreachable from the init state and the
        // network.
        let mut segment_dead = vec![false; self.segments.len()];
        let mut cycle_break_dead = vec![false; self.cycle_breaks.len()];

        // Scan nodes to initialize dead flags.
        let mut changed = false;
        for (i, seg) in self.segments.iter().enumerate() {
            if seg.preds.len() == 0 {
                segment_dead[i] = true;
                changed = true;
            }
        }
        for (i, cb) in self.cycle_breaks.iter().enumerate() {
            if cb.preds.len() == 0 {
                cycle_break_dead[i] = true;
                changed = true;
            }
        }

        if !changed {
            // No nodes are dead.
            return;
        }


        // Delete dead nodes from predecessor lists, and mark any nodes that become newly dead as a
        // result.  Running time is `O(n*m)` where `n` is the number of nodes and `m` is the length
        // of the longest path containing only dead nodes.

        fn pred_is_dead(
            segment_dead: &[bool],
            cycle_break_dead: &[bool],
            pred: &Predecessor,
        ) -> bool {
            match pred.src {
                StateSource::CpuInit => false,
                StateSource::Segment(i) => segment_dead[i],
                StateSource::Network(_) => false,
                StateSource::CycleBreak(i) => cycle_break_dead[i],
            }
        }

        /// Remove predecessors from `preds` that refer to dead nodes.  Returns `true` if `preds`
        /// was nonempty but became empty after filtering.
        fn filter_preds(
            segment_dead: &[bool],
            cycle_break_dead: &[bool],
            preds: &mut Vec<Predecessor>,
        ) -> bool {
            if preds.len() == 0 {
                return false;
            }
            preds.retain(|p| !pred_is_dead(segment_dead, cycle_break_dead, p));
            preds.len() == 0
        }

        while changed {
            changed = false;
            for (i, seg) in self.segments.iter_mut().enumerate() {
                if filter_preds(&segment_dead, &cycle_break_dead, &mut seg.preds) {
                    segment_dead[i] = true;
                    changed = true;
                }
            }
            for (i, cb) in self.cycle_breaks.iter_mut().enumerate() {
                if filter_preds(&segment_dead, &cycle_break_dead, &mut cb.preds) {
                    cycle_break_dead[i] = true;
                    changed = true;
                }
            }
        }

        // Delete `NetworkInputNode`s whose predecessor is dead.  These are handled separately
        // since they need different handling.  Only one pass is needed here since these nodes have
        // no successors.
        let to_net = &mut self.to_net;
        self.network_inputs.retain(|n| {
            let dead = pred_is_dead(&segment_dead, &cycle_break_dead, &n.pred);
            if dead {
                to_net.remove(&n.segment_index);
            }
            !dead
        });
    }

    /// Initialize secrets needed for evaluation of intermediate values.
    fn init_secrets(&mut self, b: &Builder<'a>, trace: &[TraceChunk]) {
        // Initialize edge liveness flags.

        // Keep the set of live edges for use when setting CycleBreak states.
        let mut live_edges = HashSet::new();
        live_edges.insert(Liveness::Always);
        for (pred, succ) in trace.iter().zip(trace[1..].iter()) {
            let mut src = pred.segment;
            if let Some(ref d) = succ.debug {
                if d.clear_prev_segment {
                    continue;
                }
                if let Some(prev_segment) = d.prev_segment {
                    src = prev_segment;
                }
            }
            let dest = succ.segment;

            if let Some(ref edge) = self.edges.get(&(src, dest)) {
                // `edge` is the liveness flag for the direct edge from `src` to `dest`.
                edge.set(b, true);
                live_edges.insert(Liveness::Edge(src, dest));
            } else {
                // There is no direct edge, so this connection must go through the routing network.
                // We set the liveness flags for both sides, and record the input/output indices so
                // the path through the network can be enabled once the network is constructed.
                let src_to_net = self.to_net.get(&src)
                    .unwrap_or_else(|| panic!("no outgoing edge from {} to {}", src, dest));
                let dest_from_net = self.from_net.get(&dest)
                    .unwrap_or_else(|| panic!("no incoming edge from {} to {}", src, dest));
                src_to_net.set(b, true);
                dest_from_net.set(b, true);
                live_edges.insert(Liveness::ToNetwork(src));
                live_edges.insert(Liveness::FromNetwork(dest));

                self.network_conns.push((src, dest));
            }
        }

        // Use default values (`false`) for all unused edge liveness flags.
        let it = self.edges.values()
            .chain(self.from_net.values())
            .chain(self.to_net.values());
        for s in it {
            s.apply_default();
        }

        // Set secrets for all CycleBreak nodes.  For `CycleBreak -> Segment` edges, set the secret
        // to the segment's initial state; for `Segment -> CycleBreak`, set it to the final state.
        // Every CycleBreak should be covered by one of these cases; if this doesn't hold, the
        // trace will likely be marked invalid due to a CycleBreak state being defaulted to the
        // wrong value.

        let mut set_cycle_breaks = HashSet::new();

        let mut prev_state = self.cpu_init_state.clone();
        for chunk in trace {
            let mut init_state = prev_state;
            if let Some(ref d) = chunk.debug {
                if let Some(ref state) = d.prev_state {
                    init_state = state.clone();
                }
                if let Some(cycle) = d.cycle {
                    init_state.cycle = cycle;
                }
            }

            for pred in &self.segments[chunk.segment].preds {
                if !live_edges.contains(&pred.live) {
                    continue;
                }
                match pred.src {
                    StateSource::CycleBreak(i) => {
                        if set_cycle_breaks.insert(i) {
                            self.cycle_breaks[i].secret.set(b, init_state.clone());
                        }
                    },
                    _ => {},
                }
            }

            prev_state = chunk.states.last().expect("empty chunk").clone();
            prev_state.cycle = init_state.cycle + chunk.states.len() as u32;
        }

        for (i, cbn) in self.cycle_breaks.iter().enumerate() {
            for pred in &cbn.preds {
                if !live_edges.contains(&pred.live) {
                    continue;
                }
                match pred.src {
                    StateSource::Segment(j) => {
                        if set_cycle_breaks.insert(i) {
                            let state = trace[j].states.last().expect("empty chunk").clone();
                            cbn.secret.set(b, state);
                        }
                    },
                    _ => {},
                }
            }
        }

        // Use default values for all unused cycle-break nodes.
        for cbn in &self.cycle_breaks {
            cbn.secret.apply_default();
        }
    }

    /// Get the order in which to construct the segment circuits.  This ordering is guaranteed to
    /// respect dependencies between the segments.  Specifically, calling `get_initial` on element
    /// `k` of the ordering is guaranteed to succeed if `set_final` has been called on all elements
    /// prior to `k`.
    pub fn get_order(&self) -> impl Iterator<Item = SegGraphItem> {
        // Compute a postorder traversal of the graph.  This way each node is processed only after
        // all its predecessors have been processed.

        // If a segment's `done` flag is set, then it has already been inserted into `order`, and
        // doesn't need to be traversed again.
        let mut done = vec![false; self.segments.len()];

        enum Step {
            Enter(usize),
            Exit(usize),
        }

        let mut stack = Vec::new();
        let mut order = Vec::with_capacity(self.segments.len());
        let mut num_dead = 0;
        for i in 0 .. self.segments.len() {
            if done[i] {
                continue;
            }
            stack.push(Step::Enter(i));
            while let Some(step) = stack.pop() {
                match step {
                    Step::Enter(i) => {
                        stack.push(Step::Exit(i));
                        for pred in &self.segments[i].preds {
                            match pred.src {
                                StateSource::Segment(j) => {
                                    if !done[j] {
                                        stack.push(Step::Enter(j));
                                    }
                                },
                                _ => {},
                            }
                        }
                    },
                    Step::Exit(i) => {
                        // Only include non-dead nodes in the order.
                        if self.segments[i].preds.len() > 0 {
                            order.push(i);
                        } else {
                            num_dead += 1;
                        }
                        done[i] = true;
                    },
                }
            }
            debug_assert!(stack.len() == 0);
        }
        debug_assert!(order.len() + num_dead == self.segments.len());

        order.into_iter().map(SegGraphItem::Segment)
            .chain(iter::once(SegGraphItem::Network))
    }

    /// Obtain the initial state to use for a given segment.
    pub fn get_initial(&mut self, b: &Builder<'a>, idx: usize) -> TWire<'a, RamState> {
        let _g = b.scoped_label(format_args!("seg_graph/get_initial/{}", idx));
        let mut it = self.segments[idx].preds.iter();
        let first_pred = it.next()
            .unwrap_or_else(|| panic!("segment {} has no predecessors", idx));
        let first = self.get_predecessor(b, *first_pred);
        let state = it.fold(first, |acc, pred| {
            let state = self.get_predecessor(b, *pred);
            b.mux(state.live, state, acc)
        });
        state
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
                NetworkState::After(ref net) => &net[id.into_raw()],
            },
            StateSource::CycleBreak(idx) =>
                self.cycle_breaks[idx].secret.wire(),
        }
    }

    fn count_final_mem_users(&mut self) {
        let mut pred_idxs = Vec::new();
        for i in 0..self.segments.len() {
            if !self.segments[i].has_initial_mem() {
                continue;
            }

            for pred in &self.segments[i].preds {
                match pred.src {
                    StateSource::CpuInit => { self.cpu_init_mem.add_user(); },
                    StateSource::Segment(j) => pred_idxs.push(j),
                    _ => {},
                }
            }
            for &j in &pred_idxs {
                self.segments[j].final_mem.add_user();
            }
            pred_idxs.clear();
        }
    }

    /// Obtain the initial memory state for segment `idx`.
    ///
    /// To avoid expensive clones, this method returns ownership of the memory state.  As a result,
    /// this method will panic if it's called multiple times with the same `idx`.
    pub fn take_initial_mem(&mut self, idx: usize) -> KnownMem<'a> {
        assert!(!self.segments[idx].took_initial_mem,
            "duplicate call to take_initial_mem({})", idx);
        if !self.segments[idx].has_initial_mem() {
            return KnownMem::new();
        }

        let mut mem: Option<KnownMem> = None;
        for j in 0 .. self.segments[idx].preds.len() {
            let pred = &self.segments[idx].preds[j];
            let pred_mem = match pred.src {
                StateSource::CpuInit => self.cpu_init_mem.take(),
                StateSource::Segment(j) => self.segments[j].final_mem.take(),
                _ => continue,
            };

            match mem {
                Some(ref mut mem) => mem.merge(&pred_mem),
                None => { mem = Some(pred_mem.into_owned()); },
            }
        }
        mem.unwrap()
    }

    pub fn set_final_mem(&mut self, idx: usize, mem: KnownMem<'a>) {
        self.segments[idx].final_mem.set(mem);
    }

    pub fn set_cpu_init_mem(&mut self, mem: KnownMem<'a>) {
        self.cpu_init_mem.set(mem);
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
        let mut routing = routing.finish_with_default(b, default);

        for &(src, dest) in &self.network_conns {
            let src_input = self.segments[src].to_net
                .unwrap_or_else(|| panic!("no outgoing edge from {} to {}", src, dest));
            let dest_output = self.segments[dest].from_net
                .unwrap_or_else(|| panic!("no incoming edge from {} to {}", src, dest));
            routing.connect(src_input, dest_output);
        }

        let outputs = routing.finish(b);
        self.network = NetworkState::After(outputs);
    }

    pub fn finish(mut self, cx: &Context<'a>, b: &Builder<'a>) {
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
                .map_or_else(|| b.lit(false), |s| s.live);
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


        // Special handling for CpuInit.

        // Sanity check: there should be exactly one incoming edge from CpuInit.
        let cpu_init_count = self.segments.iter().flat_map(|n| n.preds.iter())
            .chain(self.cycle_breaks.iter().flat_map(|n| n.preds.iter()))
            .filter(|p| p.src == StateSource::CpuInit).count();
        assert_eq!(cpu_init_count, 1);


        self.panic_on_drop.defuse();
    }
}

impl<'a> SegmentNode<'a> {
    fn has_initial_mem(&self) -> bool {
        for pred in &self.preds {
            match pred.src {
                StateSource::CpuInit => {},
                StateSource::Segment(_) => {},
                // `Network`/`CycleBreak` always has unknown initial memory state, and merging
                // unknown with anything produces unknown.  Thus there's no point in computing an
                // initial memory for segments with these predecessors.
                StateSource::Network(_) |
                StateSource::CycleBreak(_) => return false,
            }
        }

        true
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SegGraphItem {
    Segment(usize),
    Network,
}


#[derive(Debug, Migrate)]
struct PanicOnDrop {
    defused: bool,
}

impl PanicOnDrop {
    pub fn new() -> PanicOnDrop {
        PanicOnDrop { defused: false }
    }

    pub fn defuse(&mut self) {
        self.defused = true;
    }
}

impl Drop for PanicOnDrop {
    fn drop(&mut self) {
        assert!(self.defused, "must call finish() before dropping SegGraphBuilder");
    }
}


/// A value of type `T`, along with a user count, which limits how many times `take()` can be
/// called.  The last user gets ownership of the `T`; all other users get a reference instead.
#[derive(Default)]
struct Counted<T> {
    /// The wrapped value, if it has been set.
    ///
    /// **Invariant**:  If `user_count` is zero, then `value` is `None`.
    value: Option<T>,
    user_count: usize,
}

impl<T: Clone> Counted<T> {
    pub fn new() -> Counted<T> {
        Counted {
            value: None,
            user_count: 0,
        }
    }

    pub fn add_user(&mut self) {
        self.user_count += 1;
    }

    pub fn set(&mut self, value: T) {
        assert!(self.value.is_none(), "multiple calls to set_value");
        if self.user_count > 0 {
            self.value = Some(value);
        }
    }

    pub fn take(&mut self) -> Cow<T> {
        assert!(self.user_count > 0, "called take() too many times");
        assert!(self.value.is_some(), "called take() before set");
        self.user_count -= 1;
        if self.user_count == 0 {
            Cow::Owned(self.value.take().unwrap())
        } else {
            Cow::Borrowed(self.value.as_ref().unwrap())
        }
    }
}

impl<'a, 'b, T: Migrate<'a, 'b>> Migrate<'a, 'b> for Counted<T> {
    type Output = Counted<T::Output>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Counted<T::Output> {
        Counted {
            value: v.visit(self.value),
            user_count: self.user_count,
        }
    }
}
