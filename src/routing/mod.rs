use std::ops::Index;
use std::u32;
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{TWire, TSecretHandle, Builder, Repr, Lit, Mux};

mod benes;
pub mod sort;


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
pub struct InputId(usize);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
pub struct OutputId(usize);

impl InputId {
    pub fn into_raw(self) -> usize {
        self.0
    }
}

impl OutputId {
    pub fn into_raw(self) -> usize {
        self.0
    }
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
        let bn = benes::BenesNetwork::new(n as u32, n as u32);
        let (outputs, secrets) = benes_build(b, &bn, self.inputs, self.num_outputs);
        Routing {
            bn,
            outputs,
            secrets,
            connected_a: vec![false; n],
            connected_b: vec![false; n],
            routes: Vec::with_capacity(n),
        }
    }
}

impl<'a, T: Repr<'a>> Default for RoutingBuilder<'a, T> {
    fn default() -> RoutingBuilder<'a, T> {
        RoutingBuilder::new()
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
        }
    }
}


pub struct Routing<'a, T: Repr<'a>> {
    bn: benes::BenesNetwork,
    outputs: Vec<TWire<'a, T>>,
    secrets: Vec<Option<TSecretHandle<'a, bool>>>,

    connected_a: Vec<bool>,
    connected_b: Vec<bool>,
    routes: Vec<benes::Route>,
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
        assert!(!self.connected_a[inp.0], "input {:?} is already connected", inp);
        assert!(!self.connected_b[out.0], "output {:?} is already connected", out);
        self.connected_a[inp.0] = true;
        self.connected_b[out.0] = true;
        self.routes.push(benes::Route {
            input: inp.0 as u32,
            output: out.0 as u32,
            public: false,
        });
    }

    /// Set the secret routing bits.  Returns the outputs for further use.
    pub fn finish(mut self, b: &Builder<'a>) -> Vec<TWire<'a, T>> {
        self.bn.set_routes(&self.routes);
        if b.is_prover() {
            for (sh, &flags) in self.secrets.into_iter().zip(self.bn.flags.iter()) {
                if let Some(sh) = sh {
                    sh.set(b, flags.contains(benes::SwitchFlags::F_SWAP));
                }
            }
        }

        self.outputs
    }
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
    bn: &benes::BenesNetwork,
    inputs: Vec<TWire<'a, T>>,
    num_outputs: usize,
) -> (Vec<TWire<'a, T>>, Vec<Option<TSecretHandle<'a, bool>>>)
where T: Mux<'a, bool, T, Output = T>, T::Repr: Clone {
    if inputs.len() <= 1 {
        return (inputs, Vec::new());
    }

    assert!(inputs.len() <= 2 * bn.layer_size);
    let num_inputs = inputs.len();
    let mut ws = inputs.into_iter().map(Some)
        .chain((num_inputs .. 2 * bn.layer_size).map(|_| None))
        .collect::<Vec<_>>();
    debug_assert!(ws.len() == 2 * bn.layer_size);
    let mut secrets = Vec::with_capacity(bn.num_layers * bn.layer_size);
    for l in 0 .. bn.num_layers {
        let mut new_ws = Vec::with_capacity(bn.layer_size);
        for i in 0 .. bn.layer_size {
            let [j0, j1] = bn.switch(l, i);
            let (out0, out1, sh) = match (ws[j0 as usize].clone(), ws[j1 as usize].clone()) {
                (Some(inp0), Some(inp1)) => {
                    let (out0, out1, sh) = maybe_swap(b, inp0, inp1);
                    (Some(out0), Some(out1), Some(sh))
                },
                (Some(inp0), None) => {
                    (Some(inp0.clone()), Some(inp0), None)
                },
                (None, Some(inp1)) => {
                    (Some(inp1.clone()), Some(inp1), None)
                },
                (None, None) => {
                    (None, None, None)
                },
            };
            new_ws.push(out0);
            new_ws.push(out1);
            secrets.push(sh);
        }
        assert_eq!(ws.len(), new_ws.len());
        ws = new_ws;
    }

    let outputs = ws.into_iter().take(num_outputs).enumerate()
        .map(|(i, w)| w.unwrap_or_else(|| panic!("missing output for index {}", i)))
        .collect();
    (outputs, secrets)
}


#[cfg(test)]
mod test {
    use std::convert::TryInto;
    use bumpalo::Bump;
    use log::*;
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::{Circuit, FilterNil};
    use crate::ir::typed::EvaluatorExt;
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn check_routing_circuit(perm: &[usize], n: usize) {
        // If only the first `n` inputs are real, then the permutation must send all elements >= n
        // to the same position.
        assert!(perm.iter().enumerate().skip(n).all(|(i, &j)| i == j));

        let arena = Bump::new();
        let c = Circuit::new(&arena, true, FilterNil);
        let b = Builder::new(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let mut rb = RoutingBuilder::new();
        let inputs = (0 .. n).map(|i| b.lit(i as u32)).collect::<Vec<_>>();
        let input_ids = inputs.iter().map(|&w| rb.add_input(w)).collect::<Vec<_>>();
        let output_ids = (0 .. n).map(|_| rb.add_output()).collect::<Vec<_>>();
        let mut r = rb.finish_exact(&b);
        for (i, &j) in perm[..n].iter().enumerate() {
            r.connect(input_ids[i], output_ids[j]);
        }
        let outputs = r.finish(&b);

        let output_vals = outputs.iter()
            .map(|&w| ev.eval_typed(w).unwrap().try_into().unwrap())
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
