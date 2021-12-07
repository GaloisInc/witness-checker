use std::ops::Index;
use log::*;
use crate::ir::typed::{TWire, TSecretHandle, Builder, Repr, Lit, Mux};

pub mod sort;


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct InputId(usize);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct OutputId(usize);

const NONE: usize = usize::MAX;

impl InputId {
    const NONE: InputId = InputId(NONE);
}

impl OutputId {
    const NONE: OutputId = OutputId(NONE);
}

/// A builder for constructing a routing network.  `T` is the type of values to route.  The caller
/// must provide `TWire`s for all inputs; `TWire`s for all outputs become available only after
/// calling `finish`.
pub struct RoutingBuilder<'a, T: Repr<'a>> {
    inputs: Vec<TWire<'a, T>>,
    num_outputs: usize,
}

impl<'a, T: Repr<'a>> RoutingBuilder<'a, T> {
    pub fn new() -> RoutingBuilder<'a, T> {
        RoutingBuilder {
            inputs: Vec::new(),
            num_outputs: 0,
        }
    }

    /// Add an input to the routing network.  The caller must provide a `TWire` carrying the input
    /// value.
    pub fn add_input(&mut self, inp: TWire<'a, T>) -> InputId {
        let id = InputId(self.inputs.len());
        self.inputs.push(inp);
        id
    }

    /// Add an output to the routing network.  The `TWire` carrying the output value becomes
    /// available after calling `finish`.
    pub fn add_output(&mut self) -> OutputId {
        let id = OutputId(self.num_outputs);
        self.num_outputs += 1;
        id
    }

    /// Finish building the routing network circuit.
    pub fn finish(self, b: &Builder<'a>) -> Routing<'a, T>
    where T: Mux<'a, bool, T, Output = T> + Lit<'a> + Default, T::Repr: Clone {
        self.finish_with_default(b, T::default())
    }

    /// Finish building the routing network circuit.
    pub fn finish_with_default(mut self, b: &Builder<'a>, default: T) -> Routing<'a, T>
    where T: Mux<'a, bool, T, Output = T> + Lit<'a>, T::Repr: Clone {
        let pad = b.lit(default);

        // Pad out the inputs and outputs to the same length.
        if self.inputs.len() < self.num_outputs {
            let default = pad.clone();
            self.inputs.resize_with(self.num_outputs, || default.clone());
        }

        if self.num_outputs < self.inputs.len() {
            self.num_outputs = self.inputs.len();
        }

        self.finish_exact(b)
    }

    /// Finish building the routing network circuit.  Panics if the number of inputs is not equal
    /// to the number of outputs.
    pub fn finish_exact(self, b: &Builder<'a>) -> Routing<'a, T>
    where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
        assert!(self.inputs.len() == self.num_outputs);
        let n = self.inputs.len();
        let (outputs, secrets) = benes_build(b, self.inputs);
        Routing {
            outputs,
            secrets,
            fwd: vec![OutputId::NONE; n],
            rev: vec![InputId::NONE; n],
        }
    }
}

impl<'a, T: Repr<'a>> Default for RoutingBuilder<'a, T> {
    fn default() -> RoutingBuilder<'a, T> {
        RoutingBuilder::new()
    }
}


pub struct Routing<'a, T: Repr<'a>> {
    outputs: Vec<TWire<'a, T>>,
    secrets: Vec<Vec<Option<TSecretHandle<'a, bool>>>>,

    /// For each input, the index of the connected output.
    fwd: Vec<OutputId>,
    /// For each output, the index of the connected input.
    rev: Vec<InputId>,
}

impl<'a, T: Repr<'a>> Index<OutputId> for Routing<'a, T> {
    type Output = TWire<'a, T>;
    fn index(&self, id: OutputId) -> &TWire<'a, T> {
        &self.outputs[id.0]
    }
}

impl<'a, T: Repr<'a>> Routing<'a, T> {
    /// Configure the routing network to connect `inp` to `out`.
    pub fn connect(&mut self, inp: InputId, out: OutputId) {
        assert!(
            self.fwd[inp.0] == OutputId::NONE,
            "input {:?} is already connected to {:?}", inp, self.fwd[inp.0],
        );
        assert!(
            self.rev[out.0] == InputId::NONE,
            "output {:?} is already connected to {:?}", out, self.rev[out.0],
        );
        self.fwd[inp.0] = out;
        self.rev[out.0] = inp;
    }

    /// Set the secret routing bits.  Returns the outputs for further use.
    pub fn finish(mut self, b: &Builder<'a>) -> Vec<TWire<'a, T>> {
        // Fill out the rest of the permutation.
        let fwd_unset = self.fwd.iter_mut().enumerate()
            .filter(|&(_, ref id)| **id == OutputId::NONE);
        let rev_unset = self.rev.iter_mut().enumerate()
            .filter(|&(_, ref id)| **id == InputId::NONE);
        for ((i, a), (j, b)) in fwd_unset.zip(rev_unset) {
            *a = OutputId(j);
            *b = InputId(i);
        }

        // Convert `fwd` to `Vec<usize>`, and pad to a power of two.  Within the padding, we map
        // each fake input `i` to the corresponding output `i`.
        let n = self.fwd.len();
        let size = n.next_power_of_two();
        let l2r = self.fwd.into_iter().map(|id| id.0)
            .chain(n .. size)
            .collect::<Vec<_>>();

        // Compute the routing bits and set the secrets.
        let routing = if l2r.len() >= 2 {
            benes_route(&l2r)
        } else {
            // Match the layout used by benes_build for 0- or 1-input networks.
            vec![vec![false]]
        };
        assert_eq!(routing.len(), self.secrets.len());
        for (rs, ss) in routing.into_iter().zip(self.secrets.into_iter()) {
            assert_eq!(rs.len(), ss.len());
            for (r, s) in rs.into_iter().zip(ss.into_iter()) {
                if let Some(s) = s {
                    s.set(b, r);
                }
            }
        }

        self.outputs
    }
}


/// Evaluate a Benes network, computing the output that connects to the indicated input.
#[cfg_attr(not(test), allow(unused))]
fn benes_eval(routing: &[Vec<bool>], offset: usize, size: usize, input: usize) -> usize {
    trace!("routing {} / {} (offset {}) in {:?}", input, size, offset, routing);

    assert!(input < size);
    if size == 2 {
        trace!("  input: {}", input);
        let output = if routing[0][(input + offset) / 2] {
            input ^ 1
        } else {
            input
        };
        trace!("  output: {}", output);
        return output;
    }
    assert!(size > 2);
    assert!(size.is_power_of_two());

    trace!("  input: {}", input);
    let l_swap = routing[0][(input + offset) / 2];
    let input2 = input ^ l_swap as usize;
    trace!("  input2: {}", input2);

    let mid_side = input2 & 1 == 1;
    let mid_input = input2 / 2;
    trace!("  mid_input: subnet {}, index {}", mid_side as usize, mid_input);

    let mid_offset = offset + (if mid_side { size / 2 } else { 0 });
    let mid_output = benes_eval(&routing[1 .. routing.len() - 1], mid_offset, size / 2, mid_input);
    trace!("  mid_output: subnet {}, index {}", mid_side as usize, mid_output);

    let output2 = 2 * mid_output + mid_side as usize;
    trace!("  output2: {}", output2);

    let r_swap = routing[routing.len() - 1][(output2 + offset) / 2];
    let output = output2 ^ r_swap as usize;
    trace!("  output: {}", output);

    output
}


fn maybe_swap<'a, T>(
    b: &Builder<'a>,
    x: TWire<'a, T>,
    y: TWire<'a, T>,
) -> (TWire<'a, T>, TWire<'a, T>, TSecretHandle<'a, bool>)
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    let (swap, sh) = b.secret();
    let x2 = b.mux(swap, y.clone(), x.clone());
    let y2 = b.mux(swap, x, y);
    (x2, y2, sh)
}

/// Build a Benes network for permuting `inputs`.
fn benes_build<'a, T>(
    b: &Builder<'a>,
    inputs: Vec<TWire<'a, T>>,
) -> (Vec<TWire<'a, T>>, Vec<Vec<Option<TSecretHandle<'a, bool>>>>)
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    let size = inputs.len().next_power_of_two();
    benes_build_inner(b, size, inputs)
}

fn benes_build_inner<'a, T>(
    b: &Builder<'a>,
    size: usize,
    inputs: Vec<TWire<'a, T>>,
) -> (Vec<TWire<'a, T>>, Vec<Vec<Option<TSecretHandle<'a, bool>>>>)
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    let n = inputs.len();
    trace!("benes_build: n = {}, size = {}", n, size);

    if size <= 2 {
        if n <= 1 {
            trace!("finish: n = {}, size = {}, secrets = {}x{}", n, size, 1, 1);
            return (inputs, vec![vec![None]]);
        } else if n == 2 {
            let mut it = inputs.into_iter();
            let x = it.next().unwrap();
            let y = it.next().unwrap();
            let (x, y, sh) = maybe_swap(b, x, y);
            trace!("finish: n = {}, size = {}, secrets = {}x{}", n, size, 1, 1);
            return (vec![x, y], vec![vec![Some(sh)]]);
        }
    }

    // Generate switches for the left/input side.
    let mut it = inputs.into_iter();
    // Inputs to the middle layer, for subnet 0/1.
    let mut mid_inputs0 = Vec::with_capacity((n + 1) / 2);
    let mut mid_inputs1 = Vec::with_capacity(n / 2);
    // Secrets controlling the switches on the input side.
    let mut input_secrets = Vec::with_capacity(size / 2);
    // Index of the switch, ranging over `0 .. n/2`.
    let mut ii = 0;
    while let Some(x) = it.next() {
        assert!(ii < size);
        match it.next() {
            Some(y) => {
                let (x, y, sh) = maybe_swap(b, x, y);
                mid_inputs0.push(x);
                mid_inputs1.push(y);
                input_secrets.push(Some(sh));
            },
            None => {
                // There are an odd number of inputs, and `x` is the final one.  It always goes to
                // subnet 0.
                //
                // Here's an example illustrating the handling of non-power-of-two input sizes, and
                // why the above rule is correct.  Suppose we have 5 real inputs (`input0` through
                // `input4`).  We expand this to the next power of two by adding 3 infinities
                // (`inf5` through `inf7`).  (These are logical/virtual infinities - they never
                // appear concretely in the code.)  Each infinity is left in its original position,
                // so `inf5` goes to position 5, `inf6` to 6, and `inf7` to 7.  The inputs may be
                // permuted in any manner.
                //
                // In `benes_route`, we process inputs in reverse order.  So the first loop begins
                // with `inf7`.  The first two segments of the loop are `inf7 -> 7` and `6 <-
                // inf6`.  `inf6` and `inf7` share a switch on the input side, so this is the end
                // of the loop.  Since we have arbitrarily choosen not to swap at the start of each
                // loop, `inf6` goes to subnet 0, and `inf7` goes to subnet 1.
                //
                // Next, we process `inf5`.  The first segment is `inf5 -> 5` via subnet 1.  The
                // second segment is unknown, `4 <- ??`, because it concerns a real input, which
                // may be moved arbitrarily by the permutation.  However, we know this segment must
                // use subnet 0, since `inf5 -> 5` has already claimed subnet 1.  Similarly, we
                // know the final segment of this loop, `?? <- input4`, must also use subnet 0.
                //
                // This `None` branch is the `input4` case, where we know it uses subnet 0.
                mid_inputs0.push(x);
            },
        }
        ii += 1;
    }
    input_secrets.resize_with(size / 2, || None);
    assert!(input_secrets.len() <= size / 2);

    // Build the two middle subnetworks.
    let (mid_outputs0, mid_secrets0) = benes_build_inner(b, size / 2, mid_inputs0);
    let (mid_outputs1, mid_secrets1) = benes_build_inner(b, size / 2, mid_inputs1);

    // Generate switches for the right/output side.
    let mut it0 = mid_outputs0.into_iter();
    let mut it1 = mid_outputs1.into_iter();
    let mut outputs = Vec::with_capacity(n);
    let mut output_secrets = Vec::with_capacity(size / 2);
    while let Some(x) = it0.next() {
        match it1.next() {
            Some(y) => {
                let (x, y, sh) = maybe_swap(b, x, y);
                outputs.push(x);
                outputs.push(y);
                output_secrets.push(Some(sh));
            },
            None => {
                outputs.push(x);
            },
        }
    }
    assert!(output_secrets.len() <= size / 2);
    output_secrets.resize_with(size / 2, || None);

    let mut secrets = Vec::with_capacity(mid_secrets0.len() + 2);
    secrets.push(input_secrets);
    for (s0, s1) in mid_secrets0.into_iter().zip(mid_secrets1.into_iter()){
        assert_eq!(s0.len(), size / 4);
        assert_eq!(s1.len(), size / 4);
        secrets.push(s0.into_iter().chain(s1.into_iter()).collect());
    }
    secrets.push(output_secrets);

    trace!("finish: n = {}, size = {}, secrets = {}x{:?}", n, size, secrets.len(),
        secrets.iter().map(|s| s.len()).collect::<Vec<_>>());
        //secrets[0].len());
    (outputs, secrets)
}


/// Compute the routing information to implement a permutation with a Benes network.  Each entry of
/// the returned `Vec<Vec<bool>>` corresponds to a layer of the Benes network, and each `Vec<bool>`
/// contains a bit (indicating "swap" or "don't swap") for each switch in the layer.
///
/// The permutation is provided in the list `l2r`; `l2r[i] == j` indicates that input `i` on the
/// left should be mapped to output `j` on the right.  `l2r.len()` must be a power of two.
fn benes_route(l2r: &[usize]) -> Vec<Vec<bool>> {
    let n = l2r.len();

    if n == 2 {
        trace!("route single pair");
        if l2r[0] == 0 {
            return vec![vec![false]];
        } else {
            return vec![vec![true]];
        }
    }
    assert!(n > 2);
    assert!(n.is_power_of_two(), "permutation length {} is not a power of two");

    trace!(">> begin routing {} items", n);

    let mut r2l = vec![0; n];
    for (i, &j) in l2r.iter().enumerate() {
        r2l[j] = i;
    }

    let mut l_swap = vec![false; n / 2];
    let mut r_swap = vec![false; n / 2];
    let mut seen = vec![false; n];

    let mut inner_l2r = [vec![0; n / 2], vec![0; n / 2]];

    // Process loops in reverse order.  When sorting, we pad with infinities at the end of the
    // list, and we'd like those infinities to be routed in a predictable manner.
    for i in (0 .. l2r.len()).rev() {
        if seen[i] {
            continue;
        }

        trace!("route loop starting from {}", i);
        let start = i;
        let mut i = i;
        loop {
            let j = l2r[i];
            let j2 = j ^ 1;
            let i2 = r2l[j2];
            assert!(!seen[i]);
            assert!(!seen[i2]);

            // Set up the next two segments of the loop, connecting `i` to `j` and `j2` to `i2`.
            // Which side (top or bottom) of the inner network the `i-j` segment uses is already
            // determined by `l_swap[i/2]`.  The `j2-i2` segment must use the opposite side.

            // Which side the `i-j` link uses.  `true` means bottom (index 1), `false` means top
            // (index 0).
            //
            // These three need to be equal:
            //      l_swap[i/2] ^ (i & 1)       (which subnet `i` is routed to)
            //      ij_side
            //      r_swap[j/2] ^ (j & 1)       (which subnet `j` is routed to)
            //
            // The formula `swap[k/2] ^ (k & 1)` computes which subnet input/output `k` is
            // connected to.  If `swap[k/2]` is 0 and `k & 1` is 0, then `k` is the top input to a
            // non-swapping switch, and is passed to subnet 0.
            //
            // Note that, for the first segment of a loop, `l_swap` is "uninitialized" (defaulted
            // to false in the `vec!` constructed above).  The decision of whether to swap on the
            // first switch is arbitrary, so we always choose not to swap.
            let ij_side = l_swap[i / 2] ^ (i & 1 == 1);
            // Set up `r_swap[j/2]` to make the equation hold.
            r_swap[j / 2] = ij_side ^ (j & 1 == 1);

            // Now route the `i2-j2` segment.
            let ij2_side = r_swap[j2 / 2] ^ (j2 & 1 == 1);
            l_swap[i2 / 2] = ij2_side ^ (i2 & 1 == 1);

            // Set up the inner permutation to reflect the routing we just performed.
            inner_l2r[ij_side as usize][i / 2] = j / 2;
            inner_l2r[ij2_side as usize][i2 / 2] = j2 / 2;

            trace!("  A: {} -> {} via {}", i, j, ij_side as usize);
            trace!("  B: {} <- {} via {}", i2, j2, ij2_side as usize);

            seen[i] = true;
            seen[i2] = true;

            // For the next iteration, set up the next two segments of this loop.
            i = i2 ^ 1;

            if i == start {
                break;
            }
        }
    }

    let inner0 = benes_route(&inner_l2r[0]);
    let inner1 = benes_route(&inner_l2r[1]);
    assert_eq!(inner0.len(), inner1.len());

    let mut layers = Vec::with_capacity(inner0.len() + 2);
    layers.push(l_swap);
    for (l0, l1) in inner0.into_iter().zip(inner1.into_iter()) {
        assert_eq!(l0.len(), n / 4);
        assert_eq!(l1.len(), n / 4);
        let l = l0.into_iter().chain(l1.into_iter()).collect::<Vec<_>>();
        layers.push(l);
    }
    layers.push(r_swap);

    trace!("<< end routing {} items", n);

    layers
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;
    use bumpalo::Bump;
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::Circuit;
    use crate::ir::circuit::DynCircuit;
    use crate::ir::typed::EvaluatorExt;
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    /// Check that `routing` implements the permutation given in `l2r`.
    fn benes_check_permutation(l2r: &[usize], routing: &[Vec<bool>]) {
        for (i, &j) in l2r.iter().enumerate() {
            assert_eq!(
                benes_eval(routing, 0, l2r.len(), i),
                j,
            );
        }
    }

    /// Test `benes_eval` on a manually constructed Benes network.
    #[test]
    fn test_benes_eval() {
        init();
        // Manually-constructed Benes network for the permutation 1234 -> 2314
        let routing = vec![
            vec![false, false],
            vec![true, false],
            vec![true, false],
        ];
        benes_check_permutation(&[2, 0, 1, 3], &routing);
    }

    /// Test `benes_route` on a specific example permutation of size 4.
    #[test]
    fn test_benes_route() {
        init();
        let routing = benes_route(&[2, 0, 1, 3]);
        eprintln!("routing = {:?}", routing);
        benes_check_permutation(&[2, 0, 1, 3], &routing);
    }

    /// Test `benes_route` on every permutation of size 4.
    #[test]
    fn test_benes_perms() {
        init();
        // Lazy way to enumerate permutations: just take all 4^4 combinations, and check for ones
        // that are valid permutations.
        let mut n = 0;
        for x in 0 .. 4 * 4 * 4 * 4 {
            let perm = [x & 3, (x >> 2) & 3, (x >> 4) & 3, (x >> 6) & 3];
            let mut seen = [false; 4];
            for &j in perm.iter() {
                seen[j] = true;
            }
            if seen.iter().any(|s| !s) {
                continue;
            }
            n += 1;

            eprintln!("checking {:?}", perm);
            let routing = benes_route(&perm);
            benes_check_permutation(&perm, &routing);
        }
        assert_eq!(n, 1 * 2 * 3 * 4);
    }

    /// Test `benes_route` on a larger permutation (size 32).
    #[test]
    fn test_benes_route_big() {
        init();
        let perm = [
            13, 10, 17, 11, 25, 8, 19, 9, 21, 2, 30, 23, 31, 5, 28, 7,
            4, 0, 22, 3, 29, 16, 6, 27, 26, 18, 15, 24, 12, 14, 20, 1,
        ];
        let routing = benes_route(&perm);
        benes_check_permutation(&perm, &routing);
    }

    #[test]
    fn test_benes_route_fetch_failure() {
        init();
        let perm = [0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 10, 11, 12, 13, 14, 15];
        let routing = benes_route(&perm);
        benes_check_permutation(&perm, &routing);
    }

    fn check_benes_circuit(perm: &[usize], n: usize) {
        // If only the first `n` inputs are real, then the permutation must send all elements >= n
        // to the same position.
        assert!(perm.iter().enumerate().skip(n).all(|(i, &j)| i == j));

        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let inputs = (0 .. n).map(|i| b.lit(i as u32)).collect::<Vec<_>>();
        let routing = benes_route(&perm);
        let (outputs, secrets) = benes_build(&b, inputs);
        assert_eq!(routing.len(), secrets.len());
        for (rs, ss) in routing.into_iter().zip(secrets.into_iter()) {
            assert_eq!(ss.len(), rs.len());
            for (r, s) in rs.into_iter().zip(ss.into_iter()) {
                if let Some(s) = s {
                    s.set(&b, r);
                }
            }
        }

        let output_vals = outputs.iter()
            .map(|&w| ev.eval_typed(w).unwrap().try_into().unwrap())
            .collect::<Vec<usize>>();
        trace!("outputs: {:?}", output_vals);
        for (j, i) in output_vals.into_iter().enumerate() {
            assert_eq!(perm[i], j);
        }
    }

    #[test]
    fn test_benes_circuit_small() {
        init();
        check_benes_circuit(&[2, 0, 1, 3], 3);
    }

    #[test]
    fn test_benes_circuit_big() {
        init();
        let perm = [
            4, 10, 19, 14, 16, 1, 3, 26, 18, 17, 21, 2, 11, 5, 8, 9,
            24, 12, 25, 7, 15, 6, 23, 0, 13, 20, 22,
            27, 28, 29, 30, 31,
        ];
        check_benes_circuit(&perm, 27);
    }

    #[test]
    fn test_benes_circuit_fetch_failure() {
        init();
        let perm = [0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 10, 11, 12, 13, 14, 15];
        check_benes_circuit(&perm, 9);
    }
}
