//! Implementation of Benes network construction and routing.
//!
//! This module is completely abstract: it will generate the network layout and routing
//! configuration to implement an arbitrary permutation, but it doesn't produce any actual
//! circuits.  That part is left to the parent module.
use std::cmp;
use std::convert::TryFrom;
use std::fmt::{self, Write as _};
use bitflags::bitflags;

/// A route to be taken through the network.  The given `input` will be sent to the given `output`
/// index.  If `public` is set, then the fact that these are connected is public; this can be
/// exploited in some cases to simplify the resulting circuit.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Route {
    pub input: u32,
    pub output: u32,
    pub public: bool,
}

bitflags! {
    /// Information about a given index in the `RouteTable`.
    ///
    /// Some bits of `flags[i]` apply to the A-side input at index `i`, while others apply to the
    /// B-side output at index `i`.  Flags concerning the A side and the B side are unrelated, but
    /// are stored together for efficiency.
    struct RouteTableFlags: u8 {
        /// The route involving the A-side input at this index is public.
        const RT_A_PUBLIC = 1;
        /// There is a route involving the A-side input at this index.
        const RT_A_USED = 2;
        /// There is a route involving the B-side output at this index.
        const RT_B_USED = 4;
    }
}

/// A set of routes, condensed to flat array form for quick lookups.
struct RouteTable {
    a2b: Box<[u32]>,
    b2a: Box<[u32]>,
    flags: Box<[RouteTableFlags]>,
    num_inputs: u32,
    num_outputs: u32,
}

impl RouteTable {
    /// Create a new, empty `RouteTable` for the given number of inputs and outputs.
    pub fn new(num_inputs: usize, num_outputs: usize) -> RouteTable {
        assert!(u32::try_from(num_inputs).is_ok());
        assert!(u32::try_from(num_outputs).is_ok());
        let n = cmp::max(num_inputs, num_outputs).checked_next_power_of_two()
            .expect("routing network size overflowed");

        RouteTable {
            a2b: vec![0; n].into_boxed_slice(),
            b2a: vec![0; n].into_boxed_slice(),
            flags: vec![RouteTableFlags::empty(); n].into_boxed_slice(),
            num_inputs: num_inputs as u32,
            num_outputs: num_outputs as u32,
        }
    }

    /// Remove all routes from this table.
    pub fn clear(&mut self) {
        for x in self.flags.iter_mut() {
            *x = RouteTableFlags::empty();
        }
    }

    /// Add a route from input `a` to output `b`.  If `public` is set, then the fact that `a` is
    /// connected to `b` is public information.
    pub fn connect(&mut self, a: u32, b: u32, public: bool) {
        assert!(
            !self.flags[a as usize].contains(RouteTableFlags::RT_A_USED),
            "multiple routes use input {}", a,
        );
        assert!(
            !self.flags[b as usize].contains(RouteTableFlags::RT_B_USED),
            "multiple routes use input {}", b,
        );

        self.a2b[a as usize] = b;
        self.b2a[b as usize] = a;

        self.flags[a as usize].insert(RouteTableFlags::RT_A_USED);
        self.flags[b as usize].insert(RouteTableFlags::RT_B_USED);

        if public {
            self.flags[a as usize].insert(RouteTableFlags::RT_A_PUBLIC);
        }
    }

    /// Fill in any remaining slots to complete the `RouteTable`.  After this, the `RouteTable`
    /// represents a valid permutation.  This should be called before using any accessor methods
    /// such as `a2b`.
    pub fn finish(&mut self) {
        // Add extra routes for out-of-range input/output pairs.  If an input and an output are
        // both out of range, then we can connect them together publicly.
        for i in cmp::max(self.num_inputs, self.num_outputs) as usize .. self.flags.len() {
            self.connect(i as u32, i as u32, true);
        }

        // Arbitrarily connect any remaining unused inputs and outputs.
        if self.flags.len() > 0 {
            let mut a = 0;
            let mut b = 0;
            loop {
                a = match self.flags[a as usize ..].iter()
                        .position(|f| !f.contains(RouteTableFlags::RT_A_USED)) {
                    Some(step) => a + step,
                    None => break,
                };
                b = match self.flags[b as usize ..].iter()
                        .position(|f| !f.contains(RouteTableFlags::RT_B_USED)) {
                    Some(step) => b + step,
                    None => break,
                };
                self.connect(a as u32, b as u32, false);
            }
        }

        debug_assert!(self.flags.iter().all(|f| {
            f.contains(RouteTableFlags::RT_A_USED | RouteTableFlags::RT_B_USED)
        }));
    }

    /// Get the output connected to input `a`.
    pub fn a2b(&self, a: u32) -> u32 {
        self.a2b[a as usize]
    }

    /// Get the input connected to output `b`.
    pub fn b2a(&self, b: u32) -> u32 {
        self.b2a[b as usize]
    }

    /// Check whether the path containing input `a` is public.
    pub fn a_public(&self, a: u32) -> bool {
        self.flags[a as usize].contains(RouteTableFlags::RT_A_PUBLIC)
    }
}


/// A table of loops and routes.  This is used to determine a suitable order for processing routes
/// to guarantee that the routing succeeds.
#[derive(Clone, Debug, Default)]
struct LoopTable {
    routes: Vec<(u32, u32)>,
    loops: Vec<Loop>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Loop {
    /// The index in `routes` of the first route in this loop.
    start: u32,
    /// The number of routes in this loop.
    len: u32,
    /// The first `public_len` routes of this loop are public routes; the remainder must be treated
    /// as secret.
    public_len: u32,
}

impl LoopTable {
    pub fn new() -> LoopTable {
        Self::default()
    }

    /// Remove all routes and loops from this `LoopTable`.
    pub fn clear(&mut self) {
        let LoopTable { ref mut routes, ref mut loops } = *self;
        routes.clear();
        loops.clear();
    }

    /// Add routes for all inputs and outputs in `rt` in the range `base .. base + n`.  The range
    /// must be chunk-aligned: `n` must match the chunk size of the current layer, and `base` must
    /// be a multiple of `n`.  And `rt` must be chunk-structured: every input in the chunk must be
    /// mapped to an output in the same chunk.
    pub fn add(&mut self, rt: &RouteTable, base: u32, n: u32) {
        debug_assert!(base % n == 0);
        if cfg!(debug_assertions) {
            for a in base .. base + n {
                let b = rt.a2b(a);
                debug_assert!(
                    base <= b && b < base + n,
                    "input {} maps to output {}, which is outside the chunk {} .. {}",
                    a, b, base, base + n,
                );
            }
        }

        // Keep track of which inputs in the chunk have already been included in a loop.
        let mut seen = vec![false; n as usize];
        self.routes.reserve(n as usize);

        // In `self.loops`, entries `0 .. first_public_loop` are loops from previous calls to
        // `add` (which we leave unchanged), `first_public_loop .. first_secret_loop` are new
        // public loops, and `first_secret_loop .. self.loops.len()` are new secret loops.
        // `self.loops[first_secret_loop]` is always the secret loop that starts with the best
        // public path seen so far.
        let first_public_loop = self.loops.len();
        let mut first_secret_loop = first_public_loop;

        // Buffer for flags indicating which routes in the current loop are public.
        let mut is_public = Vec::new();

        for rel_start in 0 .. n {
            let start = base + rel_start;
            if seen[(start - base) as usize] {
                continue;
            }

            // Traverse the loop until we get back to `start`.
            let mut a1 = start;
            let first_route = self.routes.len();
            is_public.clear();
            let mut num_public = 0;
            loop {
                let b1 = rt.a2b(a1);
                let b2 = b1 ^ 1;
                let a2 = rt.b2a(b2);
                let a3 = a2 ^ 1;

                // Mark the nodes we've exited as `seen`.
                seen[(a1 - base) as usize] = true;
                seen[(a2 - base) as usize] = true;
                // We don't mark `a3` since either it's equal to `start`, which has already been
                // marked, or else it will be marked on the next iteration of the loop.

                self.routes.push((a1, b1));
                self.routes.push((a2, b2));

                let a1_public = rt.a_public(a1);
                let a2_public = rt.a_public(a2);
                is_public.push(a1_public);
                is_public.push(a2_public);
                if a1_public {
                    num_public += 1;
                }
                if a2_public {
                    num_public += 1;
                }

                a1 = a3;
                if a1 == start {
                    break;
                }
            }

            let len = self.routes.len() - first_route;
            if num_public == len {
                // Insert a public loop.  We may need to swap some elements to move it before any
                // secret loops and to keep the current best public path.
                let num_secret_loops = self.loops.len() - first_secret_loop;
                if num_secret_loops >= 2 {
                    // Swap the loop at `num_secret_loops` with `num_secret_loops + 1`, so that it
                    // will still be in the "best public path" position after inserting the new
                    // public loop.
                    self.loops.swap(first_secret_loop, first_secret_loop + 1);
                }
                let i = self.loops.len();
                self.loops.push(Loop {
                    start: first_route as u32,
                    len: len as u32,
                    public_len: len as u32,
                });
                if num_secret_loops >= 1 {
                    self.loops.swap(first_secret_loop, i);
                }
                first_secret_loop += 1;
            } else {
                // Push a new secret loop at the end of the list.
                self.loops.push(Loop {
                    start: first_route as u32,
                    len: len as u32,
                    // This will be updated later with the public path.
                    public_len: 0,
                });
            }

            let (old_best_start, old_best_public_len) = match self.loops.get(first_secret_loop) {
                Some(l) => (l.start, l.public_len as usize),
                None => (0, 0),
            };
            if 0 < num_public && num_public < len && num_public >= old_best_public_len {
                // This loop contains a mix of public and non-public routes.  We look for the best
                // public path within the loop, and rotate and/or reverse the loop in order to put
                // that path at the front.

                let loop_routes = &mut self.routes[first_route..];
                debug_assert_eq!(loop_routes.len(), len);
                debug_assert_eq!(is_public.len(), len);

                // The length of the best public path within this loop.
                let mut best_len = 0;
                // The start position of the best public path within this loop.  Note this can be
                // either the first or last route in the path, depending on `best_rev`.
                let mut best_start = 0;
                // If set, the best path seen so far is reversed, starting at `best_start` and
                // moving to lower indices.
                let mut best_rev = false;

                // Special case for public paths that wrap around the end of the loop.
                if *is_public.last().unwrap() == true {
                    let start = is_public.iter().rposition(|&x| x == false).unwrap() + 1;
                    let end = is_public.iter().position(|&x| x == false).unwrap();
                    let end_minus_1 = end.checked_sub(1).unwrap_or(len - 1);

                    // This path always beats the default `best_len` of zero.
                    best_len = end + len - start;
                    best_rev = loop_routes[end_minus_1] < loop_routes[start];
                    if best_rev {
                        best_start = end_minus_1;
                    } else {
                        best_start = start;
                    }
                }

                // Normal case for public paths throughout the loop.
                let mut i = 0;
                while i < len {
                    let start = match is_public[i..].iter().position(|&x| x == true) {
                        Some(x) => x + i,
                        None => break,
                    };
                    let end = match is_public[start..].iter().position(|&x| x == false) {
                        Some(x) => x + start,
                        None => break,
                    };

                    let len = end - start;
                    let rev = loop_routes[end - 1] < loop_routes[start];
                    let start = if rev { end - 1 } else { start };
                    let better =
                        len > best_len ||
                        (len == best_len && loop_routes[start] < loop_routes[best_start]);
                    if better {
                        best_len = len;
                        best_start = start;
                        best_rev = rev;
                    }

                    i = end;
                }

                if best_len >= old_best_public_len {
                    // Rotate the public path to the start of this loop.
                    if !best_rev {
                        loop_routes.rotate_left(best_start);
                    } else {
                        loop_routes.rotate_right(len - 1 - best_start);
                        loop_routes.reverse();
                    }

                    // If this loop has a better path than `loop[first_secret_loop]` (which is the
                    // previous overall best), swap this loop into the `first_secret_loop` slot.
                    let better =
                        best_len > old_best_public_len ||
                        (best_len == old_best_public_len &&
                            self.routes[first_route] < self.routes[old_best_start as usize]);
                    if better {
                        // The previous best is reduced to a fully secret loop (no public path),
                        // and the new best gains a public path.  (Note the order here matters in
                        // the case where `i == first_secret_loop`.)
                        let i = self.loops.len() - 1;
                        self.loops[first_secret_loop].public_len = 0;
                        self.loops[i].public_len = best_len as u32;
                        self.loops.swap(first_secret_loop, i);
                    }
                }
            }
        }
    }
}


bitflags! {
    pub struct SwitchFlags: u8 {
        /// This switch is configured to swap its inputs instead of passing them through.
        const F_SWAP = 1;
        /// The swap mode of this switch is public information.
        const F_PUBLIC = 2;
        /// The state of this switch has been set and can no longer be changed.
        const F_SET = 4;
    }
}

pub struct BenesNetwork {
    pub num_layers: usize,
    /// The number of switches in each layer.  The number of inputs/outputs is `2 * layer_size`.
    pub layer_size: usize,
    pub num_inputs: u32,
    pub num_outputs: u32,
    /// A matrix of `layer_size` by `num_layers` switch nodes.  The first `layer_size` elements are
    /// the contents of layer 0.  Each node takes two inputs from the previous layer (from the
    /// indices indicated by the two `u32`s) and produces two outputs.
    pub switches: Vec<[u32; 2]>,
    pub flags: Vec<SwitchFlags>,
}

impl BenesNetwork {
    pub fn new(num_inputs: u32, num_outputs: u32) -> BenesNetwork {
        let n = cmp::max(num_inputs, num_outputs).next_power_of_two() as usize;
        if n <= 1 {
            return BenesNetwork {
                num_layers: 0,
                layer_size: 0,
                num_inputs,
                num_outputs,
                switches: Vec::new(),
                flags: Vec::new(),
            };
        }
        let num_layers = n.trailing_zeros() as usize * 2 - 1;
        let layer_size = n / 2;
        let mut bn = BenesNetwork {
            num_layers,
            layer_size,
            num_inputs,
            num_outputs,
            switches: vec![[0, 0]; num_layers * layer_size],
            flags: vec![SwitchFlags::empty(); num_layers * layer_size],
        };
        bn.init();
        bn
    }

    fn node_index(&self, layer: usize, index: usize) -> usize {
        self.layer_size * layer + index
    }

    /// Retrieve the switch node inputs for node `index` of layer `layer`.
    pub fn switch(&self, layer: usize, index: usize) -> [u32; 2] {
        self.switches[self.node_index(layer, index)]
    }

    pub fn switch_mut(&mut self, layer: usize, index: usize) -> &mut [u32; 2] {
        let i = self.node_index(layer, index);
        &mut self.switches[i]
    }

    pub fn flags(&self, layer: usize, index: usize) -> SwitchFlags {
        self.flags[self.node_index(layer, index)]
    }

    pub fn flags_mut(&mut self, layer: usize, index: usize) -> &mut SwitchFlags {
        let i = self.node_index(layer, index);
        &mut self.flags[i]
    }

    fn init(&mut self) {
        // https://en.wikipedia.org/wiki/File:Benesnetwork.png
        //
        // This function implements non-recursive construction of a Benes network.  A Benes network
        // on 8 inputs has 5 layers.  Our job is to generate a list of input indices for the
        // switches in each layer.  The first layer is trivial: it just takes in all the network's
        // inputs in order.
        //
        // The remaining 4 layers can be divided into symmetrical pairs.  The connections between
        // layer 0 and layer 1 are the mirror image of the connections between layers 3 and 4, and
        // similarly for the 1-2 and 2-3 connections.  We generate these pairs together, since
        // given the input indices for layer 1, it's easy to generate the inputs for layer 4 by
        // flipping those connections.
        //
        // The inner layers of the network have a repetitive structure, arising from the recursive
        // definition of Benes networks.  For our purposes, we consider each layer to be built out
        // of a number of "chunks", where each chunk has the same arrangement of connections to the
        // corresponding chunk of the previous layer.  Layer 1 (the outermost nontrivial layer)
        // always consists of a single chunk.  Moving inward splits each chunk in half, so layer 2
        // (in networks where it isn't the mirror of a previous layer) consists of 2 identical
        // chunks, each containing half of the switches of the overall layer.  Similarly, layer 3
        // has 4 identical chunks, layer 4 has 8 chunks, and so on.

        // Trivial initialization of layer 0.
        for i in 0 .. self.layer_size {
            *self.switch_mut(0, i) = [i as u32 * 2, i as u32 * 2 + 1];
        }

        let n = (self.num_layers - 1) / 2;
        let mut buf = Vec::new();
        for l in 0 .. n {
            let l1 = 1 + l;
            let l2 = self.num_layers - 1 - l;
            // Initialize layers `l1` and `l2`, which are mirror images of each other.

            let num_chunks = 1 << l;
            // Number of switches in a single chunk.
            let chunk_size = self.layer_size >> l;
            assert!(num_chunks * chunk_size == self.layer_size);

            // Compute the input indices for the first chunk of `l1`.
            buf.clear();
            for i in 0 .. chunk_size {
                buf.push(i as u32 * 2);
            }
            for i in 0 .. chunk_size {
                buf.push(i as u32 * 2 + 1);
            }

            // Set up connections for all chunks in the layer.
            for chunk in 0 .. num_chunks {
                // All indices within this chunk are offset by `base`.
                let base = u32::try_from(chunk * chunk_size * 2).unwrap();

                for (y, &x) in buf.iter().enumerate() {
                    let y = y as u32;
                    // `x` is the source index, in the inputs to `l1`.  `y` is the destination
                    // index, in `l1` itself.  The roles are reversed for `l2`.

                    self.switch_mut(l1, (base + y) as usize / 2)[y as usize % 2] = base + x;
                    self.switch_mut(l2, (base + x) as usize / 2)[x as usize % 2] = base + y;
                }
            }
        }
    }

    /// Set the routes for this network.  This must be called only once, with a list of all the
    /// desired routes; calling it more than once will cause a panic.
    pub fn set_routes(&mut self, routes: &[Route]) {
        // The routing algorithm for Benes networks has a recursive structure, though we implement
        // it iteratively here.  In a single level of the recursion, we view the network as having
        // four parts: a layer on the A side, a layer on the B side, and two identical chunks in
        // the middle (each having half as many inputs and outputs as the overall network).  We
        // assign each route to either the upper or lower chunk, configure the A and B layers to
        // connect each of the network's inputs and outputs to the assigned chunk, and recursively
        // apply the routing algorithm to the inner chunks.
        //
        // The algorithm processes one "loop" at a time, instead of one route at a time.  A loop is
        // a cycle in the undirected graph where the nodes are inputs and outputs and there are
        // edges (1) between the input and the output of each route and (2) between each pair of
        // inputs and each pair of outputs that are connected to the same switch.  Processing a
        // loop at a time guarantees that all routes can be satisfied simultaneously by assigning
        // routes alternately to the upper and lower chunks.  (Unfortunately I've lost the citation
        // for this fact.)
        //
        // For example, given the routes `I1->O2, I2->O3, I3->O1, I4->O4`, there is only a single
        // loop (up to rotation and mirroring): `I1->O2 - O1<-I3 - I4->O4 - O3<-I2`.  The `->`/`<-`
        // edges indicate a route being traversed forward or backward, and the `-` edges indicate
        // jumping to the other input/output that uses the same switch.  For example, outputs `O1`
        // and `O2` are outputs of the same switch, so the loop includes the edge `O2 - O1`.  We
        // can either assign `I1->O2` and `I3->O1` to the upper chunk and `I2->O3` and `I4->O4` to
        // the lower or vice versa.
        //
        // As an additional complication, we add a distinction between public routes and secret
        // routes.  Making some routes public reduces the final circuit size, but taking advantage
        // of public routes requires that all public routes are processed before any secret routes.
        // This is not always possible, due to the requirement that each loop be processed in full
        // before any other routes are processed.  We handle this by processing any all-public
        // loops first, then process the longest remaining connected path of public loops, and
        // finally treat all remaining public loops as secret.  This is the best we can do, since
        // the verifier can't tell whether two unconnected public routes are part of the same loop
        // or not.

        let n = cmp::max(self.num_inputs, self.num_outputs).next_power_of_two() as usize;
        if n <= 1 {
            return;
        }

        // Build the `RouteTable` for the overall network.
        let mut rt = RouteTable::new(self.num_inputs as usize, self.num_outputs as usize);
        for r in routes {
            assert!(r.input < self.num_inputs, "input {} out of range", r.input);
            assert!(r.output < self.num_outputs, "output {} out of range", r.output);
            rt.connect(r.input, r.output, r.public);
        }
        rt.finish();
        if cfg!(debug_assertions) {
            for r in routes {
                debug_assert_eq!(rt.a2b(r.input), r.output);
                debug_assert_eq!(rt.b2a(r.output), r.input);
            }
        }


        let (mut l0, mut l1) = (0, self.num_layers - 1);
        let mut lt = LoopTable::new();
        loop {
            let size = 1 << ((l1 - l0) / 2);

            // Divide the routes in `rt` into loops, producing the `LoopTable` `lt`.
            lt.clear();
            for base in (0 .. n).step_by(size * 2) {
                lt.add(&rt, base as u32, size as u32 * 2);
            }

            if cfg!(debug_assertions) {
                for &(a, b) in &lt.routes {
                    debug_assert_eq!(rt.a2b(a), b);
                    debug_assert_eq!(rt.b2a(b), a);
                }

                let mut saw_secret = false;
                let mut count = 0;
                let chunk_size = n as u32 >> l0;
                for l in &lt.loops {
                    if saw_secret && l.public_len > 0 {
                        panic!("saw public routes after secret routes");
                    }
                    if l.public_len < l.len {
                        saw_secret = true;
                    }

                    count += l.len;
                    assert!(
                        count <= chunk_size,
                        "uneven number of routes {} for chunk size {}",
                        count, chunk_size,
                    );
                    if count == chunk_size {
                        count = 0;
                        saw_secret = false;
                    }
                }
            }

            // For each route in each loop, configure the `l0` and `l1` layers for that route, and
            // add to `rt` a route for the inner layers (`l0 + 1` through `l1 - 1`) to complete the
            // connection.
            rt.clear();
            for l in &lt.loops {
                let mut start = l.start as usize;
                let public_end = start + l.public_len as usize;
                let end = start + l.len as usize;
                if l.public_len > 0 {
                    for &(a, b) in &lt.routes[start .. public_end] {
                        self.add_route(&mut rt, l0, l1, a, b, true);
                    }
                    start = public_end;
                }
                for &(a, b) in &lt.routes[start .. end] {
                    self.add_route(&mut rt, l0, l1, a, b, false);
                }
            }

            if l0 == l1 {
                break;
            }
            l0 += 1;
            l1 -= 1;
        }

        if cfg!(debug_assertions) {
            for r in routes {
                debug_assert_eq!(
                    self.eval(r.output), r.input,
                    "failed to connect {} to {}", r.input, r.output,
                );
            }

            std::fs::write("benes.svg", self.dump_svg(None).unwrap()).unwrap();
        }
    }

    /// Configure the switches in layers `l0` and `l1` as needed for the route from `l0`'s input
    /// `a` to `l1`'s output `b`.  If `public` is set, then the resulting switch settings are
    /// public.
    fn add_route(
        &mut self,
        rt: &mut RouteTable,
        l0: usize,
        l1: usize,
        a: u32,
        b: u32,
        public: bool,
    ) {
        // Note: this method assumes that the network represented by `switches` is a Benes network
        // as generated by `init`, so it does not consult `switches` directly and also won't work
        // on any other network structure.

        // Absolute indices of the A and B switches, for use with `self.flags()` etc.
        let (ai, bi) = (a as usize / 2, b as usize / 2);
        // Layer numbers for the A and B sides, for use with `self.flags()` etc.
        let (al, bl) = (l0, l1);
        // Which side of the switch (0 or 1) the A input / B output is on.  This is the index
        // of the input/output among the two inputs/outputs of the switch.
        let (a_side, b_side) = (a % 2, b % 2);

        if al == bl {
            // Base case: for a single layer, just set the state of the single relevant switch.
            // There's nothing to add to `rt`.
            debug_assert_eq!(ai, bi, "can't connect {} to {} in a single layer", a, b);
            let swap = a_side != b_side;
            self.set_switch(al, ai, swap, public);
            return;
        }

        // Recursive case: Set the switches in the outer layers `al` and `bl`, and add a route
        // through the inner layers to `rt`.  (Note we actually implement this algorithm
        // iteratively, with the loop in `set_routes`.)

        // Mask of possible inner chunks to use.  Bit 0 is set if the top/0 chunk can be used, and
        // bit 1 is set if the bottom/1 chunk can be used.
        let mask =
            self.switch_allowed_sides(al, ai, a_side) &
            self.switch_allowed_sides(bl, bi, b_side);
        assert!(
            mask != 0,
            "can't connect {} to {} across layers {} .. {}\n\
             - layer {} switch {} flags = {:?}\n\
             - layer {} switch {} flags = {:?}",
            a, b, l0, l1,
            al, ai, self.flags(al, ai),
            bl, bi, self.flags(bl, bi),
        );

        // Which side/chunk we have chosen to use.  We arbitrarily prefer the top chunk when
        // both are possible.
        let side = if mask & 1 == 1 { 0 } else { 1 };
        let a_swap = a_side != side;
        let b_swap = b_side != side;
        self.set_switch(al, ai, a_swap, public);
        self.set_switch(bl, bi, b_swap, public);

        // Add a route through the chosen inner chunk, to be set up by the next iteration.
        let n = cmp::max(self.num_inputs, self.num_outputs).next_power_of_two();
        let depth = l0;
        let chunk_size = n >> depth;
        let a_base = a & !(chunk_size - 1);
        let b_base = b & !(chunk_size - 1);
        assert_eq!(
            a_base, b_base,
            "{} and {} are not in the same chunk of size {}", a, b, chunk_size,
        );
        let base = a_base;

        let inner_base = base + (if side == 1 { chunk_size / 2 } else { 0 });
        let inner_a = inner_base + (a - base) / 2;
        let inner_b = inner_base + (b - base) / 2;
        rt.connect(inner_a, inner_b, public);
    }

    /// Get a bitmask indicating which outputs (or inputs) this switch can send the given input (or
    /// output) to.  If the switch isn't set yet, then it can send to either output; otherwise, it
    /// can only connect inputs to outputs as determined by its swap flag.
    fn switch_allowed_sides(&self, l: usize, i: usize, which: u32) -> u8 {
        let flags = self.flags(l, i);
        if !flags.contains(SwitchFlags::F_SET) {
            0b11
        } else {
            if flags.contains(SwitchFlags::F_SWAP) == (which == 0) {
                // Swapped and which == 0, or unswapped and which == 1
                0b10
            } else {
                // Unswapped and which == 0, or swapped and which == 1
                0b01
            }
        }
    }

    /// Set the `F_SWAP` and `F_PUBLIC` flags of switch `i` in layer `l` according to the values of
    /// `swap` and `public`.  This marks the switch as `F_SET`, meaning its swap flag has been
    /// determined.  Panics if the switch is already `F_SET` but we would need to change its swap
    /// flag.
    fn set_switch(&mut self, l: usize, i: usize, swap: bool, public: bool) {
        let flags = self.flags_mut(l, i);
        if !flags.contains(SwitchFlags::F_SET) {
            flags.insert(SwitchFlags::F_SET);
            if swap {
                flags.insert(SwitchFlags::F_SWAP);
            }
        } else {
            assert_eq!(flags.contains(SwitchFlags::F_SWAP), swap);
        }

        // A non-public switch setting can later be made public.
        if public {
            flags.insert(SwitchFlags::F_PUBLIC);
        }
    }


    /// Find the input index that is connected to a given output.  The `bool` is true if all
    /// switches along the route have public swap flags.
    #[allow(dead_code)]
    pub fn eval(&self, b: u32) -> u32 {
        let mut x = b;
        for l in (0 .. self.num_layers).rev() {
            let i = x as usize / 2;
            let flags = self.flags(l, i);

            let mut side = x % 2;
            if flags.contains(SwitchFlags::F_SWAP) {
                side ^= 1;
            }

            x = self.switch(l, i)[side as usize];
        }
        x
    }

    pub fn eval_steps(&self, b: u32) -> Vec<u32> {
        let mut xs = Vec::with_capacity(self.num_layers + 1);
        let mut x = b;
        xs.push(x);
        for l in (0 .. self.num_layers).rev() {
            let i = x as usize / 2;
            let flags = self.flags(l, i);

            let mut side = x % 2;
            if flags.contains(SwitchFlags::F_SWAP) {
                side ^= 1;
            }

            x = self.switch(l, i)[side as usize];
            xs.push(x);
        }
        xs.reverse();
        xs
    }


    #[allow(dead_code)]
    fn dump(&self) -> String {
        let mut s = String::new();
        for i in 0 .. self.num_layers {
            writeln!(s, "layer {}:", i).unwrap();
            for j in 0 .. self.layer_size {
                writeln!(
                    s, "  switch {}: inputs {:?}, flags {:?}",
                    j, self.switch(i, j), self.flags(i, j),
                ).unwrap();
            }
        }
        s
    }

    #[allow(dead_code)]
    pub fn dump_svg(&self, highlight_b: Option<u32>) -> Result<String, fmt::Error> {
        let xs = match highlight_b {
            Some(b) => self.eval_steps(b),
            None => Vec::new(),
        };
        let highlight_color = |l, i, side| {
            if !xs.is_empty() && xs[l + 1] == (i * 2 + side) as u32 {
                "red"
            } else {
                "black"
            }
        };

        let mut s = String::new();
        writeln!(s, "<?xml version='1.0' encoding='UTF-8' standalone='no'?>")?;
        writeln!(
            s, "<svg width='{}' height='{}' xmlns='http://www.w3.org/2000/svg'>",
            self.num_layers * 200,
            self.layer_size * 75 + 25,
        )?;
        for l in 0..self.num_layers {
            for i in 0..self.layer_size {
                let [j0, j1] = self.switch(l, i);
                let flags = self.flags(l, i);
                writeln!(
                    s, "<rect x='{}' y='{}' width='100' height='50' \
                        style='stroke: black; stroke-width: 3px; fill: {}' />",
                    l * 200 + 50, i * 75 + 25,
                    if !flags.contains(SwitchFlags::F_SET) { "#cccccc" }
                    else if flags.contains(SwitchFlags::F_PUBLIC) { "#ccccff" }
                    else { "#ffcccc" },
                )?;

                if flags.contains(SwitchFlags::F_SET) {
                    let x0 = l * 200 + 50;
                    let x1 = l * 200 + 50 + 100;
                    let y0 = i * 75 + 25 + 15;
                    let y1 = i * 75 + 25 + 35;

                    let (ya0, ya1) = if flags.contains(SwitchFlags::F_SWAP) {
                        (y1, y0)
                    } else {
                        (y0, y1)
                    };

                    writeln!(
                        s, "<path d='M {},{} L {},{}' \
                            style='stroke: {}; stroke-width: 3px' />",
                        x0, ya0, x1, y0, highlight_color(l, i, 0),
                    )?;

                    writeln!(
                        s, "<path d='M {},{} L {},{}' \
                            style='stroke: {}; stroke-width: 3px' />",
                        x0, ya1, x1, y1, highlight_color(l, i, 1),
                    )?;
                }

                if l > 0 {
                    let x0 = (l - 1) * 200 + 50 + 100;
                    let x1 = l * 200 + 50;
                    writeln!(
                        s, "<path d='M {},{} L {},{}' \
                            style='stroke: {}; stroke-width: 3px' />",
                        x0, (j0 / 2) * 75 + 25 + if j0 % 2 == 0 { 15 } else { 35 },
                        x1, i * 75 + 25 + 15,
                        highlight_color(l, i, 0 ^ flags.contains(SwitchFlags::F_SWAP) as usize),
                    )?;
                    writeln!(
                        s, "<path d='M {},{} L {},{}' \
                            style='stroke: {}; stroke-width: 3px' />",
                        x0, (j1 / 2) * 75 + 25 + if j1 % 2 == 0 { 15 } else { 35 },
                        x1, i * 75 + 25 + 35,
                        highlight_color(l, i, 1 ^ flags.contains(SwitchFlags::F_SWAP) as usize),
                    )?;
                }
            }
        }
        writeln!(s, "</svg>")?;
        Ok(s)
    }
}


#[cfg(test)]
mod test {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn benes_test_permutation(l2r: &[usize]) {
        let num_outputs = l2r.iter().cloned().max().map(|x| x + 1).unwrap_or(0);
        let mut bn = BenesNetwork::new(l2r.len() as u32, num_outputs as u32);
        let routes = l2r.iter().enumerate().map(|(i,&j)| Route {
            input: i as u32,
            output: j as u32,
            public: false,
        }).collect::<Vec<_>>();
        bn.set_routes(&routes);

        for (i, &j) in l2r.iter().enumerate() {
            assert_eq!(bn.eval(j as u32), i as u32);
        }
    }

    /// Test `benes_route` on every permutation of size N.
    #[test]
    fn test_benes_perms() {
        init();
        const N: usize = 5;
        let count = (1..=N).product();

        for i in 0 .. count {
            let mut pool = [0; N];
            for j in 0..N {
                pool[j] = j;
            }

            let mut perm = [0; N];
            let mut x = i;
            for j in (0 .. N).rev() {
                let k = x % (j + 1);
                x /= j + 1;
                // Like `perm[j] = pool.swap_remove(k)`
                perm[j] = pool[k];
                pool[k] = pool[j];
            }

            println!("checking {:?}", perm);
            benes_test_permutation(&perm);
        }
    }

    /// Test `benes_route` on a larger permutation (size 32).
    #[test]
    fn test_benes_small() {
        init();
        let perm = [
            2, 0, 1, 3
        ];
        benes_test_permutation(&perm);
    }

    /// Test `benes_route` on a larger permutation (size 32).
    #[test]
    fn test_benes_big() {
        init();
        let perm = [
            13, 10, 17, 11, 25, 8, 19, 9, 21, 2, 30, 23, 31, 5, 28, 7,
            4, 0, 22, 3, 29, 16, 6, 27, 26, 18, 15, 24, 12, 14, 20, 1,
        ];
        benes_test_permutation(&perm);
    }

    #[test]
    fn test_benes_fetch_failure() {
        init();
        let perm = [0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 10, 11, 12, 13, 14, 15];
        benes_test_permutation(&perm);
    }

    /// Make sure we get valid networks for all combinations of public/secret flags.
    #[test]
    fn test_benes_public_routes() {
        init();
        let perms = [
            [0, 1, 2, 3, 4, 5, 6, 7],
            [4, 7, 3, 5, 1, 0, 6, 2],
        ];
        for &perm in &perms {
            for mask in 0 .. (1 << 8) {
                let mut bn = BenesNetwork::new(8, 8);
                let routes = perm.iter().enumerate().map(|(i, &j)| Route {
                    input: i as u32,
                    output: j as u32,
                    public: mask & (1 << i) != 0,
                }).collect::<Vec<_>>();
                bn.set_routes(&routes);

                for (i, &j) in perm.iter().enumerate() {
                    let b = j as u32;
                    let a = bn.eval(b);
                    assert_eq!(a, i as u32);
                    // We don't check that the route from `a` to `b` is public, since it might not
                    // be: if there are several public routes in different loops, then some of
                    // those routes will be converted to secret.
                }
            }
        }
    }
}
