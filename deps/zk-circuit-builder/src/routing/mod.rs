use std::convert::TryFrom;
use std::u32;
use crate::ir::circuit::{CircuitTrait, Wire, Ty, Bits};
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{
    TWire, Builder, BuilderExt, Repr, Lit, Mux, RawBits, FlatBits, LazySecret, SecretDep,
    FromWireList, ToWireList,
};

mod benes;
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
    where T: Mux<'a, bool, T, Output = T> + Lit<'a> + Default, T::Repr: Clone {
        self.finish_with_default(b, T::default())
    }

    /// Finish building the routing network circuit.
    pub fn finish_with_default(mut self, b: &impl Builder<'a>, default: T) -> FinishRouting<'a, T>
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
    pub fn finish_exact(self, b: &impl Builder<'a>) -> FinishRouting<'a, T>
    where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
        assert!(self.inputs.len() == self.num_outputs);
        let n = self.inputs.len();

        // Public `BenesNetwork`, which computes only the arrangement of switches.
        let mut bn = benes::BenesNetwork::new(n as u32, n as u32);
        if n >= 2 {
            bn.set_routes(&[]);
        }

        // Secret `BenesNetwork` flags.
        let num_flags = bn.num_layers * bn.layer_size;
        debug_assert_eq!(Bits::DIGIT_BITS, 32);
        let digits = (num_flags + Bits::DIGIT_BITS - 1) / Bits::DIGIT_BITS;
        let secret_swap_flags = b.secret_derived_sized(&[digits], self.routes, move |routes| {
            let mut bn = benes::BenesNetwork::new(n as u32, n as u32);
            if n >= 2 {
                let routes = routes.into_iter()
                    .filter(|&(_, _, cond)| cond)
                    .map(|(inp, out, _)| {
                        benes::Route {
                            input: inp.0,
                            output: out.0,
                            public: false,
                        }
                    }).collect::<Vec<_>>();
                bn.set_routes(&routes);
            }
            debug_assert_eq!(bn.num_layers * bn.layer_size, num_flags);

            let mut out = vec![0; digits];
            for (i, flags) in bn.flags.iter().enumerate() {
                let idx = i / Bits::DIGIT_BITS;
                let off = i % Bits::DIGIT_BITS;
                if flags.contains(benes::SwitchFlags::F_SWAP) {
                    out[idx] |= 1 << off;
                }
            }
            FlatBits(out)
        });
        let secret_swap_flags: TWire<RawBits> = b.cast(secret_swap_flags);

        let ws = self.inputs.into_iter().map(Some)
            .chain((n .. 2 * bn.layer_size).map(|_| None))
            .collect::<Vec<_>>();

        FinishRouting {
            bn,
            ws,
            secret_swap_flags,
            num_outputs: self.num_outputs,
            layer: 0,
        }
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
    bn: benes::BenesNetwork,
    ws: Vec<Option<TWire<'a, T>>>,
    secret_swap_flags: TWire<'a, RawBits>,
    num_outputs: usize,
    layer: usize,
}

impl<'a, T> FinishRouting<'a, T>
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    pub fn trivial(b: &impl Builder<'a>, ws: Vec<TWire<'a, T>>) -> FinishRouting<'a, T> {
        let num_outputs = ws.len();
        FinishRouting {
            bn: benes::BenesNetwork::new(0, 0),
            ws: ws.into_iter().map(Some).collect(),
            secret_swap_flags: b.lit(RawBits),
            num_outputs,
            layer: 0,
        }
    }

    /// Check whether `self` is ready to produce a final result.
    pub fn is_ready(&self) -> bool {
        self.layer == self.bn.num_layers
    }

    /// Run one step of circuit construction.
    pub fn step(&mut self, b: &impl Builder<'a>) {
        assert!(self.layer < self.bn.num_layers);
        let bn = &self.bn;
        let ws = &mut self.ws;
        let l = self.layer;

        let mut new_ws = Vec::with_capacity(bn.layer_size);
        for i in 0 .. bn.layer_size {
            let [j0, j1] = bn.switch(l, i);
            let (out0, out1) = match (ws[j0 as usize].take(), ws[j1 as usize].take()) {
                (Some(inp0), Some(inp1)) => {
                    let (out0, out1) = benes_switch(
                        b, inp0, inp1, bn, self.secret_swap_flags, l, i);
                    (Some(out0), Some(out1))
                },
                (Some(inp0), None) => {
                    (Some(inp0.clone()), Some(inp0))
                },
                (None, Some(inp1)) => {
                    (Some(inp1.clone()), Some(inp1))
                },
                (None, None) => {
                    (None, None)
                },
            };
            new_ws.push(out0);
            new_ws.push(out1);
        }

        assert_eq!(ws.len(), new_ws.len());
        self.ws = new_ws;
        self.layer += 1;
    }

    /// Finish circuit construction and return the final result.
    pub fn finish(self) -> Vec<TWire<'a, T>> {
        assert!(self.is_ready());
        self.ws.into_iter().take(self.num_outputs).enumerate()
            .map(|(i, w)| w.unwrap_or_else(|| panic!("missing output for index {}", i)))
            .collect()
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
            bn: self.bn,
            ws: v.visit(self.ws),
            secret_swap_flags: TWire::new(v.visit(self.secret_swap_flags.repr)),
            num_outputs: self.num_outputs,
            layer: self.layer,
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
