use std::convert::TryFrom;
use std::u32;
use crate::ir::circuit::{CircuitTrait, CircuitExt, Wire, Ty, Bits};
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{
    self, TWire, Builder, BuilderExt, Repr, Lit, Mux, RawBits, FlatBits, LazySecret, SecretDep,
    FromWireList, ToWireList,
};
use self::gadget::Permute;

mod benes;
pub mod gadget;
pub mod sort;


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
pub struct InputId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
pub struct OutputId(u32);

impl InputId {
    pub fn from_raw(x: u32) -> InputId {
        InputId(x)
    }

    pub fn into_raw(self) -> u32 {
        self.0
    }
}

impl OutputId {
    pub fn from_raw(x: u32) -> OutputId {
        OutputId(x)
    }

    pub fn into_raw(self) -> u32 {
        self.0
    }
}

impl<'a> Repr<'a> for InputId {
    type Repr = Wire<'a>;
}

impl<'a> Lit<'a> for InputId {
    fn lit(bld: &impl Builder<'a>, a: InputId) -> Wire<'a> {
        bld.lit(a.0).repr
    }
}

impl<'a> FromWireList<'a> for InputId {
    fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u32::expected_num_wires(sizes)
    }
    fn for_each_expected_wire_type<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        f: impl FnMut(Ty<'a>),
    ) {
        u32::for_each_expected_wire_type(c, sizes, f);
    }
    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        u32::build_repr_from_wires(c, sizes, build_wire)
    }
}

impl<'a> LazySecret<'a> for InputId {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u32::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        u32::word_len(&self.0)
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        u32::push_words(&self.0, out);
    }
}

impl<'a> ToWireList<'a> for InputId {
    fn num_wires(x: &Self::Repr) -> usize {
        u32::num_wires(x)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        u32::for_each_wire(x, f);
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        u32::num_sizes(x)
    }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {
        u32::for_each_size(x, f);
    }
}

impl<'a> SecretDep<'a> for InputId {
    type Decoded = InputId;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Self {
        InputId(u32::from_bits_iter(sizes, bits))
    }
}

impl<'a> Repr<'a> for OutputId {
    type Repr = Wire<'a>;
}

impl<'a> Lit<'a> for OutputId {
    fn lit(bld: &impl Builder<'a>, a: OutputId) -> Wire<'a> {
        bld.lit(a.0).repr
    }
}

impl<'a> FromWireList<'a> for OutputId {
    fn expected_num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u32::expected_num_wires(sizes)
    }
    fn for_each_expected_wire_type<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        f: impl FnMut(Ty<'a>),
    ) {
        u32::for_each_expected_wire_type(c, sizes, f);
    }
    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        u32::build_repr_from_wires(c, sizes, build_wire)
    }
}

impl<'a> LazySecret<'a> for OutputId {
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        u32::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        u32::word_len(&self.0)
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        u32::push_words(&self.0, out);
    }
}

impl<'a> ToWireList<'a> for OutputId {
    fn num_wires(x: &Self::Repr) -> usize {
        u32::num_wires(x)
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        u32::for_each_wire(x, f);
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        u32::num_sizes(x)
    }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {
        u32::for_each_size(x, f);
    }
}

impl<'a> SecretDep<'a> for OutputId {
    type Decoded = OutputId;
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Self {
        OutputId(u32::from_bits_iter(sizes, bits))
    }
}


/// A builder for constructing a routing network.  `T` is the type of values to route.  The caller
/// must provide `TWire`s for all inputs; `TWire`s for all outputs become available only after
/// calling `finish`.
pub struct RoutingBuilder<'a, T: Repr<'a>> {
    inputs: Vec<TWire<'a, T>>,
    num_outputs: usize,
    /// Pairs of inputs and outputs to connect within the routing network.  If the `bool` is
    /// `false`, then this pair is ignored (useful if the number of routes to connect is secret).
    routes: TWire<'a, Vec<(InputId, OutputId, bool)>>,
    lit_true: TWire<'a, bool>,
}

impl<'a, T: Repr<'a>> RoutingBuilder<'a, T> {
    pub fn new(b: &impl Builder<'a>) -> RoutingBuilder<'a, T> {
        RoutingBuilder {
            inputs: Vec::new(),
            num_outputs: 0,
            routes: TWire::new(Vec::new()),
            lit_true: b.lit(true),
        }
    }

    /// Add an input to the routing network.  The caller must provide a `TWire` carrying the input
    /// value.
    pub fn add_input(&mut self, inp: TWire<'a, T>) -> InputId {
        let id = InputId(u32::try_from(self.inputs.len()).unwrap());
        self.inputs.push(inp);
        id
    }

    /// Add an output to the routing network.  The `TWire` carrying the output value becomes
    /// available after calling `finish`.
    pub fn add_output(&mut self) -> OutputId {
        let id = OutputId(u32::try_from(self.num_outputs).unwrap());
        self.num_outputs += 1;
        id
    }

    pub fn connect(&mut self, inp: TWire<'a, InputId>, out: TWire<'a, OutputId>) {
        self.maybe_connect(self.lit_true, inp, out);
    }

    pub fn maybe_connect(
        &mut self,
        cond: TWire<'a, bool>,
        inp: TWire<'a, InputId>,
        out: TWire<'a, OutputId>,
    ) {
        self.routes.push(TWire::new((inp, out, cond)));
    }

    /// Finish building the routing network circuit.
    pub fn finish(self, b: &impl Builder<'a>) -> FinishRouting<'a, T>
    where
        T: Mux<'a, bool, T, Output = T> + Lit<'a>,
        T: Default,
        T: ToWireList<'a> + FromWireList<'a>,
        T::Repr: Clone,
    {
        self.finish_with_default(b, T::default())
    }

    /// Finish building the routing network circuit.
    pub fn finish_with_default(mut self, b: &impl Builder<'a>, default: T) -> FinishRouting<'a, T>
    where
        T: Mux<'a, bool, T, Output = T> + Lit<'a>,
        T: ToWireList<'a> + FromWireList<'a>,
        T::Repr: Clone,
    {
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
    pub fn finish_exact(self, b: &impl Builder<'a>) -> FinishRouting<'a, T>
    where
        T: Mux<'a, bool, T, Output = T>,
        T: ToWireList<'a> + FromWireList<'a>,
        T::Repr: Clone,
    {
        FinishRouting {
            outputs: self.finish_exact_inner(b),
        }
    }

    /// Finish building the routing network circuit.  Panics if the number of inputs is not equal
    /// to the number of outputs.
    fn finish_exact_inner(self, b: &impl Builder<'a>) -> Vec<TWire<'a, T>>
    where
        T: Mux<'a, bool, T, Output = T>,
        T: ToWireList<'a> + FromWireList<'a>,
        T::Repr: Clone,
    {
        assert!(self.inputs.len() == self.num_outputs);
        let n = self.inputs.len();
        if n == 0 {
            return Vec::new();
        }

        // Secret permutation input
        let out_to_inp = b.secret_derived_sized(&[n], self.routes, move |routes| {
            let mut inp_used = vec![false; n];
            let mut out_set = vec![false; n];
            let mut out_to_inp = vec![u32::try_from(n).unwrap(); n];

            for (inp, out, cond) in routes {
                if !cond {
                    continue;
                }
                let inp = inp.into_raw();
                let out = out.into_raw();
                debug_assert!(!inp_used[inp as usize]);
                inp_used[inp as usize] = true;
                debug_assert!(!out_set[out as usize]);
                out_set[out as usize] = true;
                out_to_inp[out as usize] = inp;
            }

            // Fill in remaining entries with distinct unused inputs.
            let mut unused_inps = (0 .. n).filter(|&i| !inp_used[i]);
            for i in 0..n {
                if !out_set[i] {
                    out_to_inp[i] = unused_inps.next().unwrap() as u32;
                }
            }
            debug_assert!(unused_inps.next().is_none());

            FlatBits(out_to_inp)
        });
        let out_to_inp: TWire<RawBits> = b.cast(out_to_inp);

        let (inp_wires, sizes) = typed::to_wire_list(&self.inputs[0]);
        let wires_per_item = inp_wires.len();
        let mut wires = Vec::with_capacity(1 + n * wires_per_item);
        wires.push(out_to_inp.repr);
        wires.extend(inp_wires);
        for inp in &self.inputs[1..] {
            let (inp_wires, _inp_sizes) = typed::to_wire_list(inp);
            debug_assert_eq!(_inp_sizes, sizes);
            wires.extend(inp_wires);
        }
        debug_assert_eq!(wires.len(), 1 + n * wires_per_item);

        let c = b.circuit();
        let gk = c.intern_gadget_kind(Permute {
            items: n,
            wires_per_item,
        });
        let w_bundle = c.gadget(gk, &wires);

        let mut outputs = Vec::with_capacity(n);
        let mut out_wires = Vec::with_capacity(wires_per_item);
        for i in 0 .. n {
            for j in 0 .. wires_per_item {
                let idx = i * wires_per_item + j;
                out_wires.push(c.extract(w_bundle, idx));
            }

            outputs.push(typed::from_wire_list(c.as_base(), &out_wires, &sizes));

            out_wires.clear();
        }

        outputs
    }
}

impl<'a, 'b, T> Migrate<'a, 'b> for RoutingBuilder<'a, T>
where
    T: for<'c> Repr<'c>,
    TWire<'a, T>: Migrate<'a, 'b, Output = TWire<'b, T>>,
{
    type Output = RoutingBuilder<'b, T>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> RoutingBuilder<'b, T> {
        RoutingBuilder {
            inputs: v.visit(self.inputs),
            num_outputs: v.visit(self.num_outputs),
            routes: v.visit(self.routes),
            lit_true: v.visit(self.lit_true),
        }
    }
}


fn benes_switch<'a, T>(
    b: &impl Builder<'a>,
    x: TWire<'a, T>,
    y: TWire<'a, T>,
    bn: &benes::BenesNetwork,
    secret_swap_flags: TWire<'a, RawBits>,
    l: usize,
    i: usize,
) -> (TWire<'a, T>, TWire<'a, T>)
where
    T: Mux<'a, bool, T, Output = T>,
    T::Repr: Clone,
{
    let public_flags = bn.flags(l, i);
    if public_flags.contains(benes::SwitchFlags::F_PUBLIC) {
        if public_flags.contains(benes::SwitchFlags::F_SWAP) {
            return (y, x);
        } else {
            return (x, y);
        }
    }

    let idx = bn.node_index(l, i);
    let swap = b.secret_derived(secret_swap_flags, move |flags| {
        flags.get(idx)
    });
    let x2 = b.mux(swap, y.clone(), x.clone());
    let y2 = b.mux(swap, x, y);
    (x2, y2)
}

pub struct FinishRouting<'a, T: Repr<'a>> {
    outputs: Vec<TWire<'a, T>>,
}

impl<'a, T> FinishRouting<'a, T>
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    pub fn trivial(b: &impl Builder<'a>, ws: Vec<TWire<'a, T>>) -> FinishRouting<'a, T> {
        FinishRouting {
            outputs: ws,
        }
    }

    /// Check whether `self` is ready to produce a final result.
    pub fn is_ready(&self) -> bool {
        true
    }

    /// Run one step of circuit construction.
    pub fn step(&mut self, b: &impl Builder<'a>) {
        assert!(!self.is_ready());
        unreachable!();
    }

    /// Finish circuit construction and return the final result.
    pub fn finish(self) -> Vec<TWire<'a, T>> {
        assert!(self.is_ready());
        self.outputs
    }

    pub fn run(mut self, b: &impl Builder<'a>) -> Vec<TWire<'a, T>> {
        while !self.is_ready() {
            self.step(b);
        }
        self.finish()
    }
}


impl<'a, 'b, T> Migrate<'a, 'b> for FinishRouting<'a, T>
where
    T: for<'c> Repr<'c>,
    TWire<'a, T>: Migrate<'a, 'b, Output = TWire<'b, T>>,
{
    type Output = FinishRouting<'b, T>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> FinishRouting<'b, T> {
        FinishRouting {
            outputs: v.visit(self.outputs),
        }
    }
}


#[cfg(test)]
mod test {
    use std::convert::TryInto;
    use log::*;
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::{Arenas, Circuit, FilterNil};
    use crate::ir::typed::{BuilderImpl, EvaluatorExt};
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn check_routing_circuit(perm: &[usize], n: usize) {
        // If only the first `n` inputs are real, then the permutation must send all elements >= n
        // to the same position.
        assert!(perm.iter().enumerate().skip(n).all(|(i, &j)| i == j));

        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let mut rb = RoutingBuilder::new(b);
        let inputs = (0 .. n).map(|i| b.lit(i as u32)).collect::<Vec<_>>();
        let input_ids = inputs.iter().map(|&w| rb.add_input(w)).collect::<Vec<_>>();
        let output_ids = (0 .. n).map(|_| rb.add_output()).collect::<Vec<_>>();
        for (i, &j) in perm[..n].iter().enumerate() {
            rb.connect(b.lit(input_ids[i]), b.lit(output_ids[j]));
        }
        let outputs = rb.finish_exact(b).run(b);

        let output_vals = outputs.iter()
            .map(|&w| ev.eval_typed(&c, w).unwrap().try_into().unwrap())
            .collect::<Vec<usize>>();
        trace!("outputs: {:?}", output_vals);
        for (j, i) in output_vals.into_iter().enumerate() {
            assert_eq!(perm[i], j);
        }
    }

    #[test]
    fn test_routing_circuit_small() {
        init();
        check_routing_circuit(&[2, 0, 1, 3], 3);
    }

    #[test]
    fn test_routing_circuit_big() {
        init();
        let perm = [
            4, 10, 19, 14, 16, 1, 3, 26, 18, 17, 21, 2, 11, 5, 8, 9,
            24, 12, 25, 7, 15, 6, 23, 0, 13, 20, 22,
            27, 28, 29, 30, 31,
        ];
        check_routing_circuit(&perm, 27);
    }

    #[test]
    fn test_routing_circuit_fetch_failure() {
        init();
        let perm = [0, 2, 4, 6, 8, 1, 3, 5, 7, 9, 10, 11, 12, 13, 14, 15];
        check_routing_circuit(&perm, 9);
    }
}
