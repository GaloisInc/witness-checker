use std::cmp::Ordering;
use crate::eval::{self, CachingEvaluator};
use crate::ir::circuit::CircuitTrait;
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{
    Builder, BuilderExt, TWire, Repr, Mux, Le, Lt, EvaluatorExt, SecretDep, ToWireList,
    FromWireList,
};
use crate::routing::{RoutingBuilder, FinishRouting, InputId, OutputId};


fn sorting_permutation<T: Ord>(xs: &[T]) -> Vec<usize> {
    if xs.len() <= 1 {
        return (0 .. xs.len()).collect();
    }

    let mut r2l = (0 .. xs.len()).collect::<Vec<_>>();
    r2l.sort_by(|&i, &j| {
        xs[i].cmp(&xs[j])
    });

    let mut l2r = vec![0; xs.len()];
    for (j, i) in r2l.into_iter().enumerate() {
        l2r[i] = j;
    }

    l2r
}


pub trait Compare<'a, T: Repr<'a>> {
    fn compare(
        &self,
        bld: &impl Builder<'a>,
        x: &TWire<'a, T>,
        y: &TWire<'a, T>,
    ) -> TWire<'a, bool>;
}

/// Sort `xs`.  `compare` will be used to check that the result is sorted; it must agree with the
/// `Ord` instance for `T` or else the final check will fail.
///
/// This is a stable sort.
pub fn sort<'a, T, C: Compare<'a, T>>(
    b: &impl Builder<'a>,
    xs: &[TWire<'a, T>],
    compare: C,
) -> Sort<'a, T, C>
where
    T: Repr<'a>,
    T: ToWireList<'a> + FromWireList<'a>,
    T: Mux<'a, bool, T, Output = T>,
    <T as Repr<'a>>::Repr: Clone,
    T: Sortable<'a>,
{
    sort_by_key(b, xs, compare, |w| w)
}

/// Sort `xs` according to `f(x)`.  `compare` will be used to check that the result is sorted; it
/// must agree with `f(x).cmp(...)` or else the final check will fail.
///
/// This is a stable sort.
pub fn sort_by_key<'a, T, U, C: Compare<'a, T>, F>(
    b: &impl Builder<'a>,
    xs: &[TWire<'a, T>],
    compare: C,
    f: F,
) -> Sort<'a, T, C>
where
    T: Repr<'a>,
    T: ToWireList<'a> + FromWireList<'a>,
    T: Mux<'a, bool, T, Output = T>,
    <T as Repr<'a>>::Repr: Clone,
    U: Repr<'a>,
    U: Sortable<'a>,
    F: FnMut(TWire<'a, T>) -> TWire<'a, U>,
{
    // Sequences of length 0 and 1 are already sorted, trivially.
    if xs.len() <= 1 {
        return Sort {
            routing: FinishRouting::trivial(b, xs.to_owned()),
            compare,
        };
    }

    let mut routing = RoutingBuilder::new(b);
    let inputs = xs.iter().map(|w| routing.add_input(w.clone())).collect::<Vec<_>>();
    let outputs = (0 .. xs.len()).map(|_| routing.add_output()).collect::<Vec<_>>();

    // Require that `inputs` and `outputs` are contiguously numbered.  This lets us reduce the
    // captures of the `secret_derived` closure down to just the starting indices.
    for (i, inp) in inputs.iter().enumerate() {
        assert_eq!(inp.into_raw(), inputs[0].into_raw() + i as u32);
    }
    for (i, out) in outputs.iter().enumerate() {
        assert_eq!(out.into_raw(), outputs[0].into_raw() + i as u32);
    }
    let inp0 = inputs[0].into_raw();
    let out0 = outputs[0].into_raw();

    let ys: Vec<TWire<'a, U>> = xs.iter().cloned().map(f).collect::<Vec<_>>();
    let ys: TWire<'a, Vec<U>> = TWire::new(ys);
    let ys = U::convert_vec(ys);
    let routes = b.secret_derived_sized(&[ys.len()], ys, move |ys| {
        let perm = sorting_permutation(&ys);
        let mut routes = Vec::with_capacity(perm.len());
        for (i, j) in perm.into_iter().enumerate() {
            let inp = InputId::from_raw(inp0 + i as u32);
            let out = OutputId::from_raw(out0 + j as u32);
            routes.push((inp, out));
        }
        routes
    });
    for route in routes.repr {
        let (inp, out) = *route;
        routing.connect(inp, out);
    }

    let routing = routing.finish_exact(b);
    Sort { routing, compare }
}

/// This trait is a workaround for bugs in rustc's trait solving.  Ideally, the `sort` function
/// would have a constraint like `T: for<'b> SecretDep<'b>`, but this causes the solver to get
/// confused about `T::Repr`.  We use this trait to cover up the connection between `T` and the
/// type we use as a `SecretDep` so that typechecking of `sort` succeeds.
pub trait Sortable<'a>
where
    Self: Sized,
    Self: Repr<'a>,
    //for<'b> <Self::AsSecretDep as SecretDep<'b>>::Decoded: Ord,
{
    type Decoded: Ord;
    type AsSecretDep: for<'b> SecretDep<'b, Decoded = Self::Decoded>;
    fn convert_vec(v: TWire<'a, Vec<Self>>) -> TWire<'a, Vec<Self::AsSecretDep>>;
}

impl<'a> Sortable<'a> for u32 {
    type Decoded = u32;
    type AsSecretDep = u32;
    fn convert_vec(v: TWire<'a, Vec<u32>>) -> TWire<'a, Vec<u32>> { v }
}

pub struct Sort<'a, T: Repr<'a>, C> {
    routing: FinishRouting<'a, T>,
    compare: C,
}

impl<'a, T, C> Sort<'a, T, C>
where
    T: Mux<'a, bool, T, Output = T>,
    T: ToWireList<'a> + FromWireList<'a>,
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
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
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
