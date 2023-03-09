use std::cmp::Ordering;
use crate::eval::{self, CachingEvaluator};
use crate::ir::circuit::CircuitTrait;
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{Builder, BuilderExt, TWire, Repr, Mux, Le, Lt, EvaluatorExt};
use crate::routing::{RoutingBuilder, FinishRouting};


fn sorting_permutation<'a, C: CircuitTrait<'a> + ?Sized, T, F>(
    c: &C,
    xs: &[TWire<'a, T>],
    mut compare: F,
) -> Option<Vec<usize>>
where
    T: Repr<'a>,
    F: FnMut(&TWire<'a, T>, &TWire<'a, T>) -> TWire<'a, bool>,
{
    if xs.len() <= 1 {
        return Some((0 .. xs.len()).collect());
    }

    // `RevealSecrets` is okay here because the output is also secret.
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

    let mut r2l = (0 .. xs.len()).collect::<Vec<_>>();
    let mut try_compare = |x, y| -> Option<bool> {
        ev.eval_typed(c, compare(x, y))
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


pub trait Compare<'a, T: Repr<'a>> {
    fn compare(
        &self,
        bld: &impl Builder<'a>,
        x: &TWire<'a, T>,
        y: &TWire<'a, T>,
    ) -> TWire<'a, bool>;
}

/// Sort `xs` in-place.  `compare(a, b)` should return `true` when `a` is less than or equal to
/// `b`.
///
/// This is an unstable sort.
pub fn sort<'a, T, C: Compare<'a, T>>(
    b: &impl Builder<'a>,
    xs: &[TWire<'a, T>],
    compare: C,
) -> Sort<'a, T, C>
where
    T: Mux<'a, bool, T, Output = T>,
    T::Repr: Clone,
{
    // Sequences of length 0 and 1 are already sorted, trivially.
    if xs.len() <= 1 {
        return Sort {
            routing: FinishRouting::trivial(xs.to_owned()),
            compare,
        };
    }

    let mut routing = RoutingBuilder::new();
    let inputs = xs.iter().map(|w| routing.add_input(w.clone())).collect::<Vec<_>>();
    let outputs = (0 .. xs.len()).map(|_| routing.add_output()).collect::<Vec<_>>();

    let perm = sorting_permutation(b.circuit(), xs, |x, y| compare.compare(b, x, y));
    if let Some(ref perm) = perm {
        for (i, &j) in perm.iter().enumerate() {
            routing.connect(inputs[i], outputs[j]);
        }
    }
    let routing = routing.finish_exact(b);
    Sort { routing, compare }
}

pub struct Sort<'a, T: Repr<'a>, C> {
    routing: FinishRouting<'a, T>,
    compare: C,
}

impl<'a, T, C> Sort<'a, T, C>
where
    T: Mux<'a, bool, T, Output = T>,
    T::Repr: Clone,
    C: Compare<'a, T>,
{
    pub fn is_ready(&self) -> bool {
        self.routing.is_ready()
    }

    pub fn step(&mut self, b: &impl Builder<'a>) {
        self.routing.step(b)
    }

    /// The returned `TWire<bool>` is `true` when the output is correctly sorted.  The caller must
    /// assert it to validate the sort results; otherwise the prover may cheat by reordering `xs`
    /// arbitrarily.
    pub fn finish(self, b: &impl Builder<'a>) -> (Vec<TWire<'a, T>>, TWire<'a, bool>) {
        let output_wires = self.routing.finish();

        let mut sorted = b.lit(true);
        for (x, y) in output_wires.iter().zip(output_wires.iter().skip(1)) {
            sorted = b.and(sorted, self.compare.compare(b, x, y));
        }

        (output_wires, sorted)
    }

    pub fn run(mut self, b: &impl Builder<'a>) -> (Vec<TWire<'a, T>>, TWire<'a, bool>) {
        while !self.is_ready() {
            self.step(b);
        }
        self.finish(b)
    }
}

impl<'a, 'b, T, C> Migrate<'a, 'b> for Sort<'a, T, C>
where
    T: for<'c> Repr<'c>,
    TWire<'a, T>: Migrate<'a, 'b, Output = TWire<'b, T>>,
    C: for<'c> Compare<'c, T>,
{
    type Output = Sort<'b, T, C>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Sort<'b, T, C> {
        Sort {
            routing: v.visit(self.routing),
            compare: self.compare,
        }
    }
}


pub struct CompareLe;
impl<'a, T> Compare<'a, T> for CompareLe
where
    T: Le<'a, Output = bool>,
    T::Repr: Copy,
{
    fn compare(
        &self,
        b: &impl Builder<'a>,
        x: &TWire<'a, T>,
        y: &TWire<'a, T>,
    ) -> TWire<'a, bool> {
        b.le(*x, *y)
    }
}

pub struct CompareLt;
impl<'a, T> Compare<'a, T> for CompareLt
where
    T: Lt<'a, Output = bool>,
    T::Repr: Copy,
{
    fn compare(
        &self,
        b: &impl Builder<'a>,
        x: &TWire<'a, T>,
        y: &TWire<'a, T>,
    ) -> TWire<'a, bool> {
        b.lt(*x, *y)
    }
}


#[cfg(test)]
mod test {
    use std::convert::TryInto;
    use crate::ir::circuit::{Arenas, Circuit, FilterNil};
    use crate::ir::typed::BuilderImpl;
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn check_benes_sort(inputs: &[u32]) {
        let arenas = Arenas::new();
        let c = Circuit::new(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let ws = inputs.iter().cloned().map(|i| b.lit(i as u32)).collect::<Vec<_>>();
        let (ws, _) = sort(b, &ws, CompareLt).run(b);

        let vals = ws.iter()
            .map(|&w| ev.eval_typed(&c, w).unwrap().try_into().unwrap())
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
