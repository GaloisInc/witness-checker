use std::cmp::Ordering;
use log::*;
use num_traits::Zero;
use crate::eval::{self, Evaluator, CachingEvaluator};
use crate::ir::circuit::Circuit;
use crate::ir::typed::{Builder, TWire, Repr, Mux};


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
    swap: Option<bool>,
    x: TWire<'a, T>,
    y: TWire<'a, T>,
) -> (TWire<'a, T>, TWire<'a, T>)
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    let swap = b.secret(swap);
    let x2 = b.mux(swap, y.clone(), x.clone());
    let y2 = b.mux(swap, x, y);
    (x2, y2)
}

fn benes_build<'a, T>(
    b: &Builder<'a>,
    routing: Option<&[Vec<bool>]>,
    inputs: Vec<TWire<'a, T>>,
) -> Vec<TWire<'a, T>>
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    let size = inputs.len().next_power_of_two();
    if let Some(r) = routing {
        assert!(r.iter().all(|l| l.len() == size / 2));
    }
    benes_build_inner(b, routing, 0, size, inputs)
}

fn benes_build_inner<'a, T>(
    b: &Builder<'a>,
    routing: Option<&[Vec<bool>]>,
    offset: usize,
    size: usize,
    inputs: Vec<TWire<'a, T>>,
) -> Vec<TWire<'a, T>>
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    let n = inputs.len();
    trace!("benes_build: n = {}, offset = {}, size = {}", n, offset, size);

    if size <= 2 {
        if n <= 1 {
            return inputs;
        } else if n == 2 {
            let swap = routing.map(|r| r[0][offset / 2]);
            let mut it = inputs.into_iter();
            let x = it.next().unwrap();
            let y = it.next().unwrap();
            let (x, y) = maybe_swap(b, swap, x, y);
            return vec![x, y];
        }
    }

    // Generate switches for the left/input side.
    let mut it = inputs.into_iter();
    let mut mid_inputs0 = Vec::with_capacity((n + 1) / 2);
    let mut mid_inputs1 = Vec::with_capacity(n / 2);
    // Index of the switch, ranging over `0 .. n/2`.
    let mut ii = 0;
    while let Some(x) = it.next() {
        assert!(ii < size);
        match it.next() {
            Some(y) => {
                let swap = routing.map(|r| r[0][offset / 2 + ii]);
                let (x, y) = maybe_swap(b, swap, x, y);
                mid_inputs0.push(x);
                mid_inputs1.push(y);
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

    // Build the two middle subnetworks.
    let sub_routing = routing.map(|r| &r[1 .. r.len() - 1]);
    let mid_outputs0 = benes_build_inner(b, sub_routing, offset, size / 2, mid_inputs0);
    let mid_outputs1 = benes_build_inner(b, sub_routing, offset + size / 2, size / 2, mid_inputs1);

    // Generate switches for the right/output side.
    let mut it0 = mid_outputs0.into_iter();
    let mut it1 = mid_outputs1.into_iter();
    let mut outputs = Vec::with_capacity(n);
    let mut jj = 0;
    while let Some(x) = it0.next() {
        match it1.next() {
            Some(y) => {
                let swap = routing.map(|r| r[r.len() - 1][offset / 2 + jj]);
                let (x, y) = maybe_swap(b, swap, x, y);
                outputs.push(x);
                outputs.push(y);
            },
            None => {
                outputs.push(x);
            },
        }
        jj += 1;
    }

    trace!("finish: n = {}, offset = {}, size = {}", n, offset, size);
    outputs
}


fn sorting_permutation<'a, T, F>(
    c: &Circuit<'a>,
    xs: &mut [TWire<'a, T>],
    compare: &mut F,
) -> Option<Vec<usize>>
where
    T: Repr<'a>,
    F: FnMut(&TWire<'a, T>, &TWire<'a, T>) -> TWire<'a, bool>,
{
    if xs.len() <= 1 {
        return Some((0 .. xs.len()).collect());
    }

    // `RevealSecrets` is okay here because the output is also secret.
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(c);

    let mut r2l = (0 .. xs.len()).collect::<Vec<_>>();
    let mut try_compare = |x, y| -> Option<bool> {
        let val = ev.eval_wire(compare(x, y).repr)?.unwrap_single()?;
        Some(!val.is_zero())
    };
    // We can't bail out from inside `sort_by` closure, so we record failures separately.
    let mut ok = true;
    r2l.sort_by(|&i, &j| {
        if !ok { return Ordering::Less; }
        match try_compare(&xs[i], &xs[j]) {
            Some(true) => Ordering::Less,
            Some(false) => Ordering::Greater,
            None => {
                ok = false;
                Ordering::Less
            },
        }
    });
    if !ok {
        return None;
    }

    let mut l2r = vec![0; xs.len()];
    for (j, i) in r2l.into_iter().enumerate() {
        l2r[i] = j;
    }

    Some(l2r)
}


/// Sort `xs` in-place.  `compare(a, b)` should return `true` when `a` is less than or equal to
/// `b`.  The returned `TWire` is `true` when the output is correctly sorted.  The caller must
/// assert it to validate the sort results; otherwise the prover may cheat by reordering `xs`
/// arbitrarily.
///
/// This is an unstable sort.
pub fn sort<'a, T, F>(b: &Builder<'a>, xs: &mut [TWire<'a, T>], compare: &mut F) -> TWire<'a, bool>
where
    T: Mux<'a, bool, T, Output = T>,
    T::Repr: Clone,
    F: FnMut(&TWire<'a, T>, &TWire<'a, T>) -> TWire<'a, bool>,
{
    // Sequences of length 0 and 1 are already sorted, trivially.
    if xs.len() <= 1 {
        return b.lit(true);
    }

    let mut perm = sorting_permutation(b.circuit(), xs, compare);
    if let Some(ref mut perm) = perm {
        assert!(perm.len() == xs.len());
        let n = xs.len();
        // Pad with `i -> i` no-op entries, for the infinities.
        perm.extend(n .. n.next_power_of_two());
    }

    let routing = perm.map(|p| benes_route(&p));
    let routing = routing.as_ref().map(|r| r as &[_]);
    let inputs = xs.to_owned();
    let outputs = benes_build(b, routing, inputs);
    xs.clone_from_slice(&outputs);

    let mut sorted = b.lit(true);
    for (x, y) in xs.iter().zip(xs.iter().skip(1)) {
        sorted = b.and(sorted, compare(x, y));
    }
    sorted
}


#[cfg(test)]
mod test {
    use std::convert::TryInto;
    use bumpalo::Bump;
    use crate::ir::circuit::Circuit;
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
        let c = Circuit::new(&arena);
        let b = Builder::new(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let inputs = (0 .. n).map(|i| b.lit(i as u32)).collect::<Vec<_>>();
        let routing = benes_route(&perm);
        let outputs = benes_build(&b, Some(&routing), inputs);

        let output_vals = outputs.iter()
            .map(|&w| ev.eval_wire(w.repr).unwrap().unwrap_single().unwrap().try_into().unwrap())
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

    fn check_benes_sort(inputs: &[u32]) {
        let arena = Bump::new();
        let c = Circuit::new(&arena);
        let b = Builder::new(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut ws = inputs.iter().cloned().map(|i| b.lit(i as u32)).collect::<Vec<_>>();
        sort(&b, &mut ws, &mut |&x, &y| b.lt(x, y));

        let vals = ws.iter()
            .map(|&w| ev.eval_wire(w.repr).unwrap().unwrap_single().unwrap().try_into().unwrap())
            .collect::<Vec<usize>>();
        for (&x, &y) in vals.iter().zip(vals.iter().skip(1)) {
            assert!(x <= y);
        }
    }

    #[test]
    fn test_benes_sort_small() {
        init();
        let inputs = [1, 2, 0];
        check_benes_sort(&inputs);
    }

    #[test]
    fn test_benes_sort_big() {
        init();
        // 26 entries (not a power of two), with some repeats
        let inputs = [
            0, 17, 19, 7, 5, 4, 18, 8, 1, 13, 16, 10, 14, 12, 2, 6,
            9, 15, 11, 3,
            5, 10, 10, 10, 15, 15,
        ];
        check_benes_sort(&inputs);
    }
}
