use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter;
use std::marker::PhantomData;
use std::mem;
use log::*;
use num_bigint::BigUint;
use zki_sieve;
use zki_sieve_v3;
use crate::back::UsePlugins;
use crate::ir::circuit::Bits;
use crate::routing::benes::{self, BenesNetwork};
use super::{Sink, WireId, Time, TEMP, Source, AssertNoWrap};
use super::arith;
use super::ops;
use super::wire_alloc::WireAlloc;


mod v1;
pub use self::v1::SieveIrV1;

mod v2;
pub use self::v2::SieveIrV2;

mod v3;
pub use self::v3::SieveIrV3;

pub trait SieveIrFormat {
    type Gate: std::fmt::Debug;
    type Function;
    type Relation;
    type PublicInputs;
    type PrivateInputs;

    fn gate_constant(out: WireId, val: Vec<u8>) -> Self::Gate;
    fn gate_private(out: WireId) -> Self::Gate;
    fn gate_copy(out: WireId, a: WireId) -> Self::Gate;
    fn gate_and(out: WireId, a: WireId, b: WireId) -> Self::Gate;
    fn gate_xor(out: WireId, a: WireId, b: WireId) -> Self::Gate;
    fn gate_not(out: WireId, a: WireId) -> Self::Gate;
    fn gate_new(start: WireId, end: WireId) -> Self::Gate;
    fn gate_delete(start: WireId, end: WireId) -> Self::Gate;
    fn gate_call(
        name: String,
        outs: impl IntoIterator<Item = (WireId, WireId)>,
        ins: impl IntoIterator<Item = (WireId, WireId)>,
    ) -> Self::Gate;
    fn gate_assert_zero(w: WireId) -> Self::Gate;

    // Multi-wire variants of `gate_private` and `gate_copy`, as defined in the Phase 3 circuit IR.
    const HAS_GATE_PRIVATE_MULTI: bool = false;
    fn gate_private_multi(out: (WireId, WireId)) -> Self::Gate {
        #![allow(unused_variables)]
        panic!("gate_private_multi is not supported");
    }
    const HAS_GATE_COPY_MULTI: bool = false;
    fn gate_copy_multi(
        out: (WireId, WireId),
        a: impl IntoIterator<Item = (WireId, WireId)>,
    ) -> Self::Gate {
        #![allow(unused_variables)]
        panic!("gate_copy_multi is not supported");
    }

    fn new_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        private_count: u64,
        gates: Vec<Self::Gate>,
    ) -> Self::Function;

    const HAS_PLUGINS: bool;
    fn new_plugin_function_with_inputs(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        plugin_name: String,
        op_name: String,
        args: Vec<String>,
        public_input_count: u64,
        private_input_count: u64,
    ) -> Self::Function;
    fn new_plugin_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        plugin_name: String,
        op_name: String,
        args: Vec<String>,
    ) -> Self::Function {
        Self::new_plugin_function_with_inputs(name, outs, ins, plugin_name, op_name, args, 0, 0)
    }

    fn relation_gate_count_approx(r: &Self::Relation) -> usize;
    fn visit_relation(
        r: Self::Relation,
        visit_gate: impl FnMut(Self::Gate),
        visit_function: impl FnMut(Self::Function),
    );
}

pub struct SieveIrFunctionSink<S, IR: SieveIrFormat> {
    sink: S,
    alloc: WireAlloc,
    gates: Vec<IR::Gate>,
    private_bits: Vec<bool>,
    /// Functions in `zki_sieve_v3` representation.  This vector is drained on `flush()`.
    functions: Vec<IR::Function>,
    /// Info about function names and signatures.  This vector persists across `flush()`; it always
    /// contains all functions that have been declared so far.
    func_info: Vec<FunctionInfo>,
    func_map: HashMap<FunctionDesc, usize>,
    /// Whether we've emitted a relation message yet.  The first relation message must contain some
    /// additional data.
    emitted_relation: bool,

    // Plugins
    use_plugin_mux_v0: bool,
    use_plugin_permutation_check_v1: bool,
    use_plugin_disjunction_v0: bool,

    _marker: PhantomData<IR>,
}

pub type SieveIrV1Sink<S> = SieveIrFunctionSink<S, SieveIrV1>;
pub type SieveIrV2Sink<S> = SieveIrFunctionSink<S, SieveIrV2>;
pub type SieveIrV3Sink<S> = SieveIrFunctionSink<S, SieveIrV3>;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
enum FunctionDesc {
    LitZero(u64),
    Private(u64),
    Copy(u64),
    And(u64),
    Or(u64),
    Xor(u64),
    Not(u64),
    Add(u64),
    AddNoWrap(u64),
    Sub(u64),
    Mul(u64),
    MulNoWrap(u64),
    WideMul(u64),
    Neg(u64),
    Mux(u64),

    /// `Permute(n, m)`: permutation function from `m` inputs to `m` outputs, with each item being
    /// `n` bits.
    Permute(u64, u32),
    /// `AssertPermute(n, m)`: Assert permutation of `m` inputs and `m` permuted inputs, with each item being
    /// `n` bits.
    AssertPermute(u64, u32),
    /// `PermuteLayerShuffle(n, m, i)`: shuffle layer `l` of `Permute(n, m)`.  This is a helper
    /// function used to reduce the peak message size in the SIEVE IR output.
    PermuteLayerShuffle(u64, u32, usize),
    /// `PermuteLayerSwitches(n, m, i)`: switch layer `l` of `Permute(n, m)`.  This is a helper
    /// function used to reduce the peak message size in the SIEVE IR output.
    PermuteLayerSwitches(u64, u32, usize),
    /// `PermuteSwitch(n)`: switch function taking two `n`-bit inputs and returning two `n`-bit
    /// outputs.
    PermuteSwitch(u64),
    /// `PermuteSwitches(n, m)`: an array of `m` instances of `PermuteSwitch(n)`.
    PermuteSwitches(u64, u32),
    /// `PermuteSwitchPublic(n, swap)`: switch function with a public `swap` input.
    PermuteSwitchPublic(u64, bool),
    /// `PermuteShuffle(n, k, flip)`: the outermost shuffle of a Benes network on `2^k` `n`-bit
    /// inputs.  If `flip` is set, the shuffle is reversed; for a Benes network of a given size,
    /// the first shuffle corresponds to `flip == false` and the last shuffle corresponds to `flip
    /// == true`.
    ///
    /// This is only defined for `k >= 2`.
    PermuteShuffle(u64, u8, bool),

    Switch(Vec<(usize, BigUint)>, u64),
}

impl FunctionDesc {
    pub fn name(&self) -> String {
        match self {
            FunctionDesc::LitZero(n) => format!("lit_zero_{}", *n),
            FunctionDesc::Private(n) => format!("private_{}", *n),
            FunctionDesc::Copy(n) => format!("copy_{}", *n),
            FunctionDesc::And(n) => format!("and_{}", *n),
            FunctionDesc::Or(n) => format!("or_{}", *n),
            FunctionDesc::Xor(n) => format!("xor_{}", *n),
            FunctionDesc::Not(n) => format!("not_{}", *n),
            FunctionDesc::Add(n) => format!("add_{}", *n),
            FunctionDesc::AddNoWrap(n) => format!("add_no_wrap_{}", *n),
            FunctionDesc::Sub(n) => format!("sub_{}", *n),
            FunctionDesc::Mul(n) => format!("mul_{}", *n),
            FunctionDesc::MulNoWrap(n) => format!("mul_no_wrap_{}", *n),
            FunctionDesc::WideMul(n) => format!("wide_mul_{}", *n),
            FunctionDesc::Neg(n) => format!("neg_{}", *n),
            FunctionDesc::Mux(n) => format!("mux_{}", *n),
            FunctionDesc::Permute(n, m) => format!("permute_{}_{}", *n, *m),
            FunctionDesc::AssertPermute(n, m) => format!("assert_permute_{}_{}", *n, *m),
            FunctionDesc::PermuteLayerShuffle(n, m, l) =>
                format!("permute_layer_shuffle_{}_{}_{}", *n, *m, *l),
            FunctionDesc::PermuteLayerSwitches(n, m, l) =>
                format!("permute_layer_switches_{}_{}_{}", *n, *m, *l),
            FunctionDesc::PermuteSwitch(n) => format!("permute_switch_{}", *n),
            FunctionDesc::PermuteSwitches(n, m) =>
                format!("permute_switches_{}_{}", *n, *m),
            FunctionDesc::PermuteSwitchPublic(n, swap) =>
                format!("permute_switch_public_{}_{}", *n, *swap as u8),
            FunctionDesc::PermuteShuffle(n, k, flip) =>
                format!("permute_shuffle_{}_{}_{}", *n, *k, *flip as u8),
            FunctionDesc::Switch(branches, _max_private_input_count) => {
                let suffix = branches.iter().map(|(idx, pat)| format!("{}_{}", idx, pat)).collect::<Vec<_>>().join("_");
                format!("switch_{}", suffix)
            },
        }
    }
}

struct FunctionInfo {
    name: String,
    counts: Vec<u64>,
    num_outputs: usize,
}

impl FunctionInfo {
    fn inputs(&self) -> &[u64] {
        &self.counts[self.num_outputs..]
    }

    fn outputs(&self) -> &[u64] {
        &self.counts[0 .. self.num_outputs]
    }

    fn _sig(&self) -> (&[u64], &[u64]) {
        self.counts.split_at(self.num_outputs)
    }
}

/// Strict upper limit on the number of gates per Flatbuffers message.
const GATE_PAGE_SIZE: usize = 64 * 1024;
/// We flush at a lower limit than the `GATE_PAGE_SIZE` since we might generate many gates between
/// flushes.
const GATE_FLUSH_SIZE: usize = GATE_PAGE_SIZE - 256;

pub trait Dispatch {
    fn flush(&mut self, free_all_pages: bool);
}

impl<S, IR: SieveIrFormat> SieveIrFunctionSink<S, IR>
where Self: Dispatch, SieveIrFunctionSink<VecSink<IR>, IR>: Dispatch {
    pub fn new(sink: S, use_plugins: UsePlugins) -> SieveIrFunctionSink<S, IR> {
        SieveIrFunctionSink {
            sink,
            alloc: WireAlloc::new(vec![
                0,          // 0 (temporaries)
                1 << 4,     // 16
                1 << 6,     // 64
                1 << 8,     // 256
                1 << 11,    // 2k
                1 << 14,    // 16k
                1 << 18,    // 256k
            ]),
            gates: Vec::new(),
            private_bits: Vec::new(),
            functions: Vec::new(),
            func_info: Vec::new(),
            func_map: HashMap::new(),
            emitted_relation: false,
            use_plugin_mux_v0: use_plugins.mux_v0,
            use_plugin_permutation_check_v1: use_plugins.permutation_check_v1,
            use_plugin_disjunction_v0: use_plugins.disjunction_v0,
            _marker: PhantomData,
        }
    }

    pub fn finish(mut self) -> S {
        self.flush(true);
        self.sink
    }

    fn alloc_wires(&mut self, expire: Time, n: u64) -> WireId {
        self.alloc.alloc(expire, n, self.gates.len())
    }

    fn lit_zero_gate_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(IR::gate_constant(out + i, vec![0]));
        }
    }

    fn lit_one_gate_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(IR::gate_constant(out + i, vec![1]));
        }
    }

    fn private_gate_into(&mut self, out: WireId, n: u64) {
        if IR::HAS_GATE_PRIVATE_MULTI {
            if n > 0 {
                let first = out;
                let last = first + n - 1;
                self.gates.push(IR::gate_private_multi((first, last)));
            }
        } else {
            for i in 0 .. n {
                self.gates.push(IR::gate_private(out + i));
            }
        }
    }

    fn copy_gate_into(&mut self, out: WireId, n: u64, a: WireId) {
        if IR::HAS_GATE_COPY_MULTI {
            if n > 0 {
                let out_first = out;
                let out_last = out_first + n - 1;
                let a_first = a;
                let a_last = a_first + n - 1;
                self.gates.push(IR::gate_copy_multi(
                    (out_first, out_last),
                    iter::once((a_first, a_last)),
                ));
            }
        } else {
            for i in 0 .. n {
                self.gates.push(IR::gate_copy(out + i, a + i));
            }
        }
    }

    /// Copy `n` copies of wire `a` (a single wire) into `out .. out + n`.
    fn rep_gate_into(&mut self, out: WireId, n: u64, a: WireId) {
        if IR::HAS_GATE_COPY_MULTI {
            if n > 0 {
                let out_first = out;
                let out_last = out_first + n - 1;
                self.gates.push(IR::gate_copy_multi(
                    (out_first, out_last),
                    iter::repeat((a, a)).take(n as usize),
                ));
            }
        } else {
            for i in 0 .. n {
                self.gates.push(IR::gate_copy(out + i, a));
            }
        }
    }

    fn and_gate_into(&mut self, out: WireId, n: u64, a: WireId, b: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_and(out + i, a + i, b + i));
        }
    }

    fn xor_gate_into(&mut self, out: WireId, n: u64, a: WireId, b: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_xor(out + i, a + i, b + i));
        }
    }

    fn not_gate_into(&mut self, out: WireId, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_not(out + i, a + i));
        }
    }

    fn private_into(&mut self, out: WireId, n: u64) {
        if IR::HAS_GATE_PRIVATE_MULTI || n <= 1 {
            self.private_gate_into(out, n);
        } else {
            self.call_gate_into(out, FunctionDesc::Private(n), &[])
        }
    }

    fn copy_into(&mut self, out: WireId, n: u64, a: WireId) {
        if IR::HAS_GATE_COPY_MULTI || n <= 1 {
            self.copy_gate_into(out, n, a);
        } else {
            self.call_gate_into(out, FunctionDesc::Copy(n), &[a])
        }
    }

    /// Get a sub-sink for building function definitions.
    ///
    /// This calls `mem::take` on some fileds of `self`, so `self` should not be used while the
    /// sub-sink is alive.  Call `self.finish_sub_sink(sub_sink)` to restore the taken fields.
    fn sub_sink(&mut self) -> SieveIrFunctionSink<VecSink<IR>, IR> {
        SieveIrFunctionSink::<_, IR> {
            sink: VecSink::default(),
            alloc: WireAlloc::new(vec![]),
            gates: Vec::new(),
            private_bits: Vec::new(),
            functions: Vec::new(),
            // Move `func_info` and `func_map` into `sub_sink`, so it can access functions defined
            // previously.
            func_info: mem::take(&mut self.func_info),
            func_map: mem::take(&mut self.func_map),
            emitted_relation: false,
            use_plugin_mux_v0: self.use_plugin_mux_v0,
            use_plugin_permutation_check_v1: self.use_plugin_permutation_check_v1,
            use_plugin_disjunction_v0: self.use_plugin_disjunction_v0,
            _marker: PhantomData,
        }
    }

    fn finish_sub_sink(
        &mut self,
        mut sub_sink: SieveIrFunctionSink<VecSink<IR>, IR>,
    ) -> VecSink<IR> {
        // Move `func_map` and `func_info` from `sub_sink` back into `self`, so in the future we
        // can use any extra functions that happened to be defined by this `sub_sink`.
        self.func_map = mem::take(&mut sub_sink.func_map);
        self.func_info = mem::take(&mut sub_sink.func_info);

        sub_sink.finish()
    }

    fn collect_sub_gates(&mut self, zki_sink: VecSink<IR>) -> Vec<IR::Gate> {
        assert_eq!(zki_sink.private_inputs.len(), 0);
        //assert_eq!(zki_sink.public_inputs.len(), 0);
        let mut gates = Vec::with_capacity(
            zki_sink.relations.iter().map(IR::relation_gate_count_approx).sum());
        let functions = &mut self.functions;
        for r in zki_sink.relations {
            IR::visit_relation(
                r,
                |g| gates.push(g),
                |f| functions.push(f),
            );
        }
        gates
    }

    fn add_func_info(
        &mut self,
        desc: FunctionDesc,
        output_count: &[u64],
        input_count: &[u64],
    ) -> (usize, String) {
        let idx = self.func_info.len();
        self.func_map.insert(desc.clone(), idx);
        let name = format!("f{}_{}", idx, desc.name());
        self.func_info.push(FunctionInfo {
            name: name.clone(),
            counts: output_count.iter().cloned().chain(input_count.iter().cloned()).collect(),
            num_outputs: output_count.len(),
        });
        trace!("add_func_info({:?}) = ({:?}, {:?})", desc, idx, name);
        (idx, name)
    }

    fn add_user_func_info(
        &mut self,
        user_name: &str,
        output_count: &[u64],
        input_count: &[u64],
    ) -> (usize, String) {
        let idx = self.func_info.len();
        let name = format!("f{}_{}", idx, user_name);
        self.func_info.push(FunctionInfo {
            name: name.clone(),
            counts: output_count.iter().cloned().chain(input_count.iter().cloned()).collect(),
            num_outputs: output_count.len(),
        });
        trace!("add_user_func_info({:?}) = ({:?}, {:?})", user_name, idx, name);
        (idx, name)
    }

    fn get_function(
        &mut self,
        desc: FunctionDesc,
    ) -> usize {
        if let Some(s) = self.func_map.get(&desc) {
            return s.to_owned();
        }

        if IR::HAS_PLUGINS {
            match desc {
                FunctionDesc::Mux(n) if self.use_plugin_mux_v0 => {
                    let (idx, name) = self.add_func_info(desc, &[n], &[1, n, n]);
                    if n == 0 {
                        return idx;
                    }

                    self.functions.push(IR::new_plugin_function(
                        name,
                        [n],
                        [1, n, n],
                        "mux_v0".into(),
                        "strict".into(),
                        vec![],
                    ));
                    return idx;
                }

                FunctionDesc::AssertPermute(n, m) if self.use_plugin_permutation_check_v1 => {
                    let argc = n * m as u64;
                    let (idx, name) = self.add_func_info(desc, &[], &[argc, argc]);

                    self.functions.push(IR::new_plugin_function(
                        name,
                        [],
                        [argc, argc],
                        "permutation_check_v1".into(),
                        "assert_perm".into(),
                        vec![n.to_string()],
                    ));
                    return idx;
                }

                // The rest of the permutation gadgets should be unreachable when using the permutation plugin.
                FunctionDesc::PermuteLayerShuffle(..)
                | FunctionDesc::PermuteLayerSwitches(..)
                | FunctionDesc::PermuteSwitch(..)
                | FunctionDesc::PermuteSwitches(..)
                | FunctionDesc::PermuteSwitchPublic(..)
                | FunctionDesc::PermuteShuffle(..) =>
                {
                    if self.use_plugin_permutation_check_v1 {
                        unreachable!("{:?}", desc);
                    }
                }

                FunctionDesc::Switch(ref branches, max_private_input_count) => if self.use_plugin_disjunction_v0 {
                    // Each branch of a Switch (i.e. disjunction) must have the same signature, so it is safe to choose the first one arbitrarily.
                    let f = &self.func_info[branches[0].0];
                    
                    let output_count = f.outputs().to_owned();
                    let mut input_count = Vec::with_capacity(1 + f.inputs().len());
                    input_count.push(1);
                    input_count.extend_from_slice(f.inputs());
                    
                    let mut params = Vec::with_capacity(1 + 2 * branches.len());
                    // TODO(isweet): Support `permissive` mode at some point?                    
                    params.push("strict".into());
                    params.extend(branches.iter().flat_map(|(idx, pat)| {
                        let pat_str = pat.to_string();
                        let name_str = self.func_info[*idx].name.clone();
                        iter::once(pat_str).chain(iter::once(name_str))
                    }));
                    
                    let (idx, name) = self.add_func_info(desc, &output_count, &input_count);                                                            
                    self.functions.push(IR::new_plugin_function_with_inputs(
                        name,
                        output_count,
                        input_count,
                        SWITCH_PLUGIN_NAME.into(),
                        "switch".into(),
                        params,
                        0,
                        max_private_input_count,
                    ));

                    return idx;
                }

                _ => {}
            }
        }

        let mut sub_sink = self.sub_sink();

        let mut private_count = 0;
        let (output_count, input_count) = match desc {
            FunctionDesc::LitZero(n) => {
                let [out] = sub_sink.alloc.preallocate([n]);
                sub_sink.lit_zero_gate_into(out, n);
                (vec![n], vec![])
            },

            FunctionDesc::Private(n) => {
                let [out] = sub_sink.alloc.preallocate([n]);
                sub_sink.private_gate_into(out, n);
                private_count = n;
                (vec![n], vec![])
            },

            FunctionDesc::Copy(n) => {
                let [out, a] = sub_sink.alloc.preallocate([n, n]);
                sub_sink.copy_gate_into(out, n, a);
                (vec![n], vec![n])
            },

            FunctionDesc::And(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                sub_sink.and_gate_into(out, n, a, b);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Or(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let a_inv = sub_sink.not(TEMP, n, a);
                let b_inv = sub_sink.not(TEMP, n, b);
                let ab_inv = sub_sink.and(TEMP, n, a_inv, b_inv);
                sub_sink.not_gate_into(out, n, ab_inv);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Xor(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                sub_sink.xor_gate_into(out, n, a, b);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Not(n) => {
                let [out, a] = sub_sink.alloc.preallocate([n, n]);
                sub_sink.not_gate_into(out, n, a);
                (vec![n], vec![n])
            },

            FunctionDesc::Add(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::add(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::No);
                sub_sink.copy_gate_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::AddNoWrap(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::add(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::Yes);
                sub_sink.copy_gate_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Sub(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::sub(&mut sub_sink, TEMP, n, a, b);
                sub_sink.copy_gate_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Mul(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::mul(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::No);
                sub_sink.copy_gate_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::MulNoWrap(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::mul(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::Yes);
                sub_sink.copy_gate_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::WideMul(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([2 * n, n, n]);
                let ab = arith::wide_mul(&mut sub_sink, TEMP, n, a, b);
                sub_sink.copy_gate_into(out, 2 * n, ab);
                (vec![2 * n], vec![n, n])
            },
            FunctionDesc::Neg(n) => {
                let [out, a] = sub_sink.alloc.preallocate([n, n]);
                let a_neg = arith::neg(&mut sub_sink, TEMP, n, a);
                sub_sink.copy_gate_into(out, n, a_neg);
                (vec![n], vec![n])
            },
            FunctionDesc::Mux(n) => {
                // Note the order of the `e` and `t` arguments is reversed, for compatibility with
                // the `mux_v0` plugin.
                let [out, c, e, t] = sub_sink.alloc.preallocate([n, 1, n, n]);
                let mux = ops::mux(&mut sub_sink, TEMP, n, c, t, e);
                sub_sink.copy_gate_into(out, n, mux);
                (vec![n], vec![1, n, n])
            },

            FunctionDesc::Permute(n, m) => {
                match self.use_plugin_permutation_check_v1 {
                    true => sub_sink.permute_body_plugin(n, m),
                    false => sub_sink.permute_body(n, m),
                }
            },
            FunctionDesc::AssertPermute(_n, _m) => {
                unreachable!();
            },
            FunctionDesc::PermuteLayerShuffle(n, m, l) => {
                sub_sink.permute_layer_shuffle(n, m, l)
            },
            FunctionDesc::PermuteLayerSwitches(n, m, l) => {
                sub_sink.permute_layer_switches(n, m, l)
            },
            FunctionDesc::PermuteSwitch(n) => {
                let [out, inp] = sub_sink.alloc.preallocate([2 * n, 2 * n]);
                let swap = sub_sink.alloc_wires(TEMP, 1);
                sub_sink.private_gate_into(swap, 1);
                sub_sink.call_gate_into(out, FunctionDesc::Mux(n), &[swap, inp, inp + n]);
                sub_sink.call_gate_into(out + n, FunctionDesc::Mux(n), &[swap, inp + n, inp]);
                (vec![2 * n], vec![2 * n])
            },
            FunctionDesc::PermuteSwitches(n, m) => {
                let [out, inp] = sub_sink.alloc.preallocate([n * 2 * m as u64, n * 2 * m as u64]);
                if m <= 4 {
                    for i in 0 .. m as u64 {
                        sub_sink.call_gate_into(
                            out + n * 2 * i,
                            FunctionDesc::PermuteSwitch(n),
                            &[inp + n * 2 * i],
                        );
                    }
                } else if m.is_power_of_two() {
                    sub_sink.call_gate_into(
                        out,
                        FunctionDesc::PermuteSwitches(n, m / 2),
                        &[inp],
                    );
                    sub_sink.call_gate_into(
                        out + n * m as u64,
                        FunctionDesc::PermuteSwitches(n, m / 2),
                        &[inp + n * m as u64],
                    );
                } else {
                    // Decompose into powers of two.
                    let mut m = m;
                    let mut offset = 0;
                    while m > 0 {
                        let cur = 1 << (31 - u32::leading_zeros(m));
                        debug_assert!(cur & m == cur);
                        sub_sink.call_gate_into(
                            out + n * 2 * offset,
                            FunctionDesc::PermuteSwitches(n, cur),
                            &[inp + n * 2 * offset],
                        );
                        m -= cur;
                        offset += cur as u64;
                    }
                }
                (vec![n * 2 * m as u64], vec![n * 2 * m as u64])
            },
            FunctionDesc::PermuteSwitchPublic(n, swap) => {
                let [out, inp] = sub_sink.alloc.preallocate([2 * n, 2 * n]);
                if swap {
                    sub_sink.copy_gate_into(out, n, inp + n);
                    sub_sink.copy_gate_into(out + n, n, inp);
                } else {
                    sub_sink.copy_gate_into(out, 2 * n, inp);
                }
                (vec![2 * n], vec![2 * n])
            },
            FunctionDesc::PermuteShuffle(n, k, flip) => {
                let [out, inp] = sub_sink.alloc.preallocate([n * (1 << k), n * (1 << k)]);
                let out_to_inp = permute_shuffle_sequence(k, flip);
                for (i, &j) in out_to_inp.iter().enumerate() {
                    sub_sink.copy_into(
                        out + n * i as u64,
                        n,
                        inp + n * j as u64,
                    );
                }
                (vec![n * (1 << k)], vec![n * (1 << k)])
            },
            FunctionDesc::Switch(_branches, _max_private_input_count) => {
                // TODO(isweet): A non-plugin version of `GateKind::Switch` is difficult to support in the current design.
                //
                // The semantics of `Switch` dictate that branches which are not taken (as indicated by the guard condition)
                // are not executed. This means that the intuitive encoding of a `Switch` using a nested multiplexor is not
                // correct, because it would execute every branch. Why is that an issue?
                // 
                // First, a nested multiplexor would consume `n * k` private inputs where `n` is the number of inputs
                // consumed by a single branch and `k` is the number of branches. In contrast, the `Switch` semantics dictate
                // that it should only consume `n` inputs. Second, the multiplexor would execute the `AssertZero` gates in
                // the body of every branch. In short, the observable side effects (private input consumption and assertion failure)
                // are different.
                //
                // Accounting for the difference in private inputs isn't too hard. The logic for emitting private inputs could be
                // adjusted so that the appropriate amount of private inputs are padded into the private input stream. When producing
                // a nested multiplexor, each non-taken branch would pad the private input stream with `n` values, and the taken branch
                // would emit the real private inputs. However, ignoring the `AssertZero` gates in non-taken branches would be more
                // challenging. This would likely require rewriting each of the branches (recursively through the callgraph) so that
                // the `AssertZero` gates can be toggled on / off according to whether the branch was taken.
                //
                // For example, each branch in the nested multiplexor could be extended with an additional argument indicating whether
                // that branch was taken (call this `in_taken_branch`). Then, each `AssertZero(x)` would be rewritten to
                // `AssertZero(And(x, in_taken_branch))` so that `AssertZero` gates in non-taken branches are ignored (i.e. always hold).
                //
                // That being said, support for a non-plugin implementation of `GateKind::Switch` is possible but left to future work.
                unimplemented!()
            }
        };

        let zki_sink = self.finish_sub_sink(sub_sink);
        let (idx, name) = self.add_func_info(desc, &output_count, &input_count);

        // For functions with no outputs (e.g. `And(0)`), we record an entry in `self.func_info`
        // but don't emit an actual `zki_sieve_v3` function.
        if output_count.iter().cloned().sum::<u64>() == 0 {
            return idx;
        }

        let gates = self.collect_sub_gates(zki_sink);
        if log_enabled!(log::Level::Debug) {
            debug!("define {}:", name);
            debug!("  inputs = {:?}", input_count);
            debug!("  outputs = {:?}", output_count);
            debug!("  gates:");
            for g in &gates {
                debug!("    {:?}", g);
            }
        }

        self.functions.push(IR::new_function(
            name.clone(),
            output_count,
            input_count,
            private_count,
            gates,
        ));

        idx
    }

    fn permute_body(&mut self, n: u64, m: u32) -> (Vec<u64>, Vec<u64>) {
        // Special cases for trivial networks.
        match m {
            0 => return (vec![0], vec![0]),
            1 => {
                let [out, inp] = self.alloc.preallocate([n, n]);
                self.copy_gate_into(out, n, inp);
                return (vec![n], vec![n]);
            },
            2 => {
                let [out, inp] = self.alloc.preallocate([2 * n, 2 * n]);
                self.call_gate_into(out, FunctionDesc::PermuteSwitch(n), &[inp]);
                return (vec![2 * n], vec![2 * n]);
            },
            _ => {},
        }

        // TODO: it's inefficient to rebuild the whole `BenesNetwork` each time
        let mut bn = BenesNetwork::new(m, m);
        let m_rounded = 2 * bn.layer_size as u32;
        bn.set_routes(&[]);

        let [out, inp] = self.alloc.preallocate([n * m_rounded as u64, n * m as u64]);
        let num_wires = n * m_rounded as u64;

        // Shuffle layer 0 pads out `inp` with zeros to reach `num_wires`.
        let mut now = 0;
        let mut cur = self.alloc_wires(now + 1, num_wires);
        self.call_gate_into(cur, FunctionDesc::PermuteLayerShuffle(n, m, 0), &[inp]);

        // TODO: insert deletes between layers (use `expire`/`advance`?)
        for l in 0 .. bn.num_layers {
            if l > 0 {
                // Shuffle
                let next = self.alloc_wires(now + 1, num_wires);
                self.call_gate_into(next, FunctionDesc::PermuteLayerShuffle(n, m, l), &[cur]);

                cur = next;
                now += 1;
                self.free_expired(now);
            }

            {
                // Switches
                let next = if l < bn.num_layers - 1 {
                    self.alloc_wires(now + 1, num_wires)
                } else {
                    // Outputs of the last switch layer go directly to the function outputs.
                    out
                };
                self.call_gate_into(next, FunctionDesc::PermuteLayerSwitches(n, m, l), &[cur]);

                cur = next;
                now += 1;
                self.free_expired(now);
            }
        }

        (vec![n * m_rounded as u64], vec![n * m as u64])
    }

    fn permute_body_plugin(&mut self, n: u64, m: u32) -> (Vec<u64>, Vec<u64>) {
        let m_rounded = m.next_power_of_two();
        let num_wires = n * m_rounded as u64;

        // Allocate n * m input wires and n * m_rounded output wires
        let [out, inp1] = self.alloc.preallocate([num_wires, n * m as u64]);

        // Get output from witness
        for i in 0 .. m as u64 {
            self.private_into(out + i * n, n);
        }

        // Pad the rest of the wires with zero
        for i in m as u64 .. m_rounded as u64 {
            self.call_gate_into(out + i * n, FunctionDesc::LitZero(n), &[]);
        }

        // Allocate a dummy wire to hold to outcome of the assertion
        let assert_out = self.alloc_wires(TEMP, 0);
        
        // Call assert_permute. Assert_permute plugin doesn't have an output
        self.call_gate_into(assert_out, FunctionDesc::AssertPermute(n, m), &[inp1, out]);

        (vec![num_wires], vec![n * m as u64])
    }

    fn permute_layer_shuffle(&mut self, n: u64, m: u32, l: usize) -> (Vec<u64>, Vec<u64>) {
        let mut bn = BenesNetwork::new(m, m);
        let m_rounded = 2 * bn.layer_size as u32;
        bn.set_routes(&[]);

        if l == 0 {
            let [out, inp] = self.alloc.preallocate([n * m_rounded as u64, n * m as u64]);

            // Pad out `inp` with zeros to reach `num_wires`.
            for i in 0 .. m as u64 {
                self.copy_into(out + n * i, n, inp + n * i);
            }
            for i in m as u64 .. m_rounded as u64 {
                self.call_gate_into(out + n * i, FunctionDesc::LitZero(n), &[]);
            }

            (vec![n * m_rounded as u64], vec![n * m as u64])

        } else {
            let [out, inp] = self.alloc.preallocate([n * m_rounded as u64, n * m_rounded as u64]);

            let half_layers = bn.num_layers / 2;
            let (k, flip) = if l - 1 < half_layers {
                ((half_layers - 1) - (l - 1) + 2, false)
            } else {
                ((l - 1) - half_layers + 2, true)
            };
            let k = u8::try_from(k).unwrap();

            let idx = self.get_function(FunctionDesc::PermuteShuffle(n, k, flip));
            for item_idx in (0 .. 2 * bn.layer_size as u64).step_by(1 << k) {
                self.call_gate_idx_into(
                    out + n * item_idx,
                    idx,
                    &[inp + n * item_idx],
                );
            }

            (vec![n * m_rounded as u64], vec![n * m_rounded as u64])
        }
    }

    fn permute_layer_switches(&mut self, n: u64, m: u32, l: usize) -> (Vec<u64>, Vec<u64>) {
        let mut bn = BenesNetwork::new(m, m);
        let m_rounded = 2 * bn.layer_size as u32;
        bn.set_routes(&[]);

        let [out, inp] = self.alloc.preallocate([n * m_rounded as u64, n * m_rounded as u64]);

        let mut i = 0;
        while i < bn.layer_size {
            let flags = bn.flags(l, i);
            if !flags.contains(benes::SwitchFlags::F_PUBLIC) {
                // Handle all non-public switches in bulk.
                let start = i;
                while i < bn.layer_size &&
                        !bn.flags(l, i).contains(benes::SwitchFlags::F_PUBLIC) {
                    i += 1;
                }
                let end = i;

                self.call_gate_into(
                    out + n * 2 * start as u64,
                    FunctionDesc::PermuteSwitches(n, (end - start) as u32),
                    &[inp + n * 2 * start as u64],
                );

            } else {
                let swap = flags.contains(benes::SwitchFlags::F_SWAP);
                self.call_gate_into(
                    out + n * 2 * i as u64,
                    FunctionDesc::PermuteSwitchPublic(n, swap),
                    &[inp + n * 2 * i as u64],
                );
                i += 1;
            }
        }

        (vec![n * m_rounded as u64], vec![n * m_rounded as u64])
    }

    fn emit_call(
        &mut self,
        expire: Time,
        desc: FunctionDesc,
        args: &[WireId],
    ) -> WireId {
        let idx = self.get_function(desc);
        self.emit_call_idx(expire, idx, args)
    }

    fn emit_call_idx(
        &mut self,
        expire: Time,
        idx: usize,
        args: &[WireId],
    ) -> WireId {
        let total_out = self.func_info[idx].outputs().iter().cloned().sum();
        if total_out == 0 {
            // Function has no outputs, so there's no need to emit a call, and we can just return a
            // dummy `WireId`.
            return 0;
        }
        let out = self.alloc_wires(expire, total_out);
        self.call_gate_idx_into(out, idx, args);
        out
    }

    fn call_gate_into(
        &mut self,
        out: WireId,
        desc: FunctionDesc,
        args: &[WireId],
    ) {
        let idx = self.get_function(desc);
        self.call_gate_idx_into(out, idx, args);
    }

    fn call_gate_idx_into(
        &mut self,
        out: WireId,
        idx: usize,
        args: &[WireId],
    ) {
        let info = &self.func_info[idx];

        debug_assert_eq!(args.len(), info.inputs().len());
        let mut next_out = out;
        self.gates.push(IR::gate_call(
            info.name.clone(),
            info.outputs().iter().map(|&n| {
                let w = next_out;
                next_out += n;
                (w, w + n - 1)
            }),
            info.inputs().iter().zip(args.iter()).map(|(&n, &w)| {
                (w, w + n - 1)
            }),
        ));
    }

    /// Compute the witness of the assert_permute plugin.
    /// 
    /// # Arguments
    /// 
    /// * `num_items` - The number of items to be permuted.
    /// * `perm` - The description of the permutation. perm.0 contains the permutation vector.
    /// * `input_values` - The values to be permuted.
    /// * `wire_widths` - The bit widths of the wires of each item.
    fn permute_private_values_plugin(&mut self, num_items: u64, perm: Bits, input_values: Vec<Bits>, wire_widths: &[u64]) {
        let permutation_vector = perm.0;
        let chunk_size = wire_widths.len();
        assert_eq!(num_items as usize * chunk_size, input_values.len(), "The length of the input values vector must equal the number of items times the chunk size");

        let num_items = u32::try_from(num_items).unwrap();
        for output in 0..num_items {
            let permuted_index = permutation_vector.get(output as usize).copied().unwrap_or(0);
            for (i, &width) in wire_widths.iter().enumerate() {
                let value = input_values[permuted_index as usize * chunk_size + i];
                self.private_value(width, value);
            }
        }
    }

    fn permute_private_values_no_plugin(&mut self, num_items: u64, perm: Bits) {
        let num_items = u32::try_from(num_items).unwrap();
        let mut bn = BenesNetwork::new(num_items, num_items);
        let mut routes = Vec::with_capacity(num_items as usize);
        for output in 0 .. num_items {
            let input = perm.0.get(output as usize).copied().unwrap_or(0);
            routes.push(benes::Route { input, output, public: false });
        }
        bn.set_routes(&routes);

        for l in 0 .. bn.num_layers {
            for i in 0 .. bn.layer_size {
                let flags = bn.flags(l, i);
                if flags.contains(benes::SwitchFlags::F_PUBLIC) {
                    continue;
                }
                let swap = flags.contains(benes::SwitchFlags::F_SWAP);
                self.private_bits.push(swap);
            }
        }
    }
}

const SWITCH_PLUGIN_NAME: &str = "disjunction_v0";

impl<S, IR: SieveIrFormat> Sink for SieveIrFunctionSink<S, IR>
where Self: Dispatch, SieveIrFunctionSink<VecSink<IR>, IR>: Dispatch {
    fn lit(&mut self, expire: Time, n: u64, bits: Bits) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            let bit = bits.get(i as usize);
            self.gates.push(IR::gate_constant(w + i, vec![bit as u8]));
        }
        w
    }
    fn private(&mut self, expire: Time, n: u64) -> WireId {
        let out = self.alloc_wires(expire, n);
        self.private_into(out, n);
        out
    }
    fn private_value(&mut self, n: u64, value: Bits) {
        for i in 0 .. n {
            self.private_bits.push(value.get(i as usize));
        }
    }
    fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        let out = self.alloc_wires(expire, n);
        self.copy_into(out, n, a);
        out
    }
    fn concat_chunks(&mut self, expire: Time, entries: &[(Source, u64)]) -> WireId {
        let total = entries.iter().map(|&(_, n)| n).sum();
        let w = self.alloc_wires(expire, total);
        let mut pos = 0;
        for &(source, n) in entries {
            match source {
                Source::Zero => {
                    self.lit_zero_gate_into(w + pos, n);
                },
                Source::One => {
                    self.lit_one_gate_into(w + pos, n);
                },
                Source::Wires(a) => {
                    self.copy_gate_into(w + pos, n, a);
                },
                Source::RepWire(a) => {
                    self.rep_gate_into(w + pos, n, a);
                },
            }
            pos += n;
        }
        w
    }

    fn and(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::And(n), &[a, b])
    }
    fn or(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Or(n), &[a, b])
    }
    fn xor(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Xor(n), &[a, b])
    }
    fn not(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Not(n), &[a])
    }

    fn add(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Add(n), &[a, b])
    }
    fn add_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::AddNoWrap(n), &[a, b])
    }
    fn sub(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Sub(n), &[a, b])
    }
    fn mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Mul(n), &[a, b])
    }
    fn mul_no_wrap(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::MulNoWrap(n), &[a, b])
    }
    fn wide_mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::WideMul(n), &[a, b])
    }
    fn neg(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Neg(n), &[a])
    }

    fn mux(&mut self, expire: Time, n: u64, c: WireId, t: WireId, e: WireId) -> WireId {
        // Note the order of the `e` and `t` arguments is reversed - see `Mux` case above.
        self.emit_call(expire, FunctionDesc::Mux(n), &[c, e, t])
    }

    fn assert_zero(&mut self, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_assert_zero(a + i));
        }
    }

    fn free_expired(&mut self, now: Time) {
        for free in self.alloc.advance(now) {
            if free.start != free.end {
                self.gates.push(IR::gate_delete(free.start, free.end - 1));
            }
        }

        if self.gates.len() >= GATE_FLUSH_SIZE {
            self.flush(false);
        }
    }

    type FunctionId = usize;
    type FunctionSink = SieveIrFunctionSink<VecSink<IR>, IR>;
    fn define_function(
        &mut self,
        name: String,
        arg_ns: &[u64],
        return_n: u64,
        build: impl FnOnce(Self::FunctionSink, &[WireId]) -> (Self::FunctionSink, WireId),
    ) -> Self::FunctionId {
        let mut sub_sink = self.sub_sink();
        let [return_wire] = sub_sink.alloc.preallocate([return_n]);
        let arg_wires = sub_sink.alloc.preallocate_slice(arg_ns);

        let (mut sub_sink, out_wire) = build(sub_sink, &arg_wires);
        if return_n > 0 {
            sub_sink.copy_into(return_wire, return_n, out_wire);
        }

        let zki_sink = self.finish_sub_sink(sub_sink);

        let (idx, name) = self.add_user_func_info(&name, &[return_n], arg_ns);
        let gates = self.collect_sub_gates(zki_sink);

        self.functions.push(IR::new_function(
            name.clone(),
            iter::once(return_n),
            arg_ns.iter().cloned(),
            // TODO: properly compute private count (needed for SIEVE IR V1)
            0,
            gates,
        ));

        idx
    }
    fn call(&mut self, expire: Time, func: &Self::FunctionId, args: &[WireId]) -> WireId {
        self.emit_call_idx(expire, *func, args)
    }

    const HAS_PERMUTE: bool = true;
    fn permute(
        &mut self,
        expire: Time,
        wires_per_item: u64,
        num_items: u64,
        inputs: WireId,
    ) -> WireId {
        let num_items = u32::try_from(num_items).unwrap();
        self.emit_call(expire, FunctionDesc::Permute(wires_per_item, num_items), &[inputs])
    }

    fn permute_private_values(&mut self, num_items: u64, perm: Bits, input_values: Vec<Bits>, wire_widths: &[u64]) {
        // If the permutation plugin is available, use the `input_values` and `perm` to compute the
        // permuted values as the witness. Otherwise, use `perm` as the witness.
        if self.use_plugin_permutation_check_v1 {
            self.permute_private_values_plugin(num_items, perm, input_values, wire_widths);
        } else {
            self.permute_private_values_no_plugin(num_items, perm);
        }
    }

    const HAS_SWITCH: bool = true;
    fn switch(
        &mut self,
        expire: Time,
        cond: WireId,
        n: u64,
        branches: Vec<(&Self::FunctionId, BigUint)>,
        args: &[WireId],
        max_private_input_count: u64,
    ) -> WireId {
        let branches = branches.into_iter().map(|(idx, pat)| (*idx, pat)).collect::<Vec<_>>();
        let mut cond_with_args = (0..n).map(|i| cond + i).collect::<Vec<_>>();
        cond_with_args.extend_from_slice(args);
        self.emit_call(expire, FunctionDesc::Switch(branches, max_private_input_count), &cond_with_args)
    }
}


/// Return the connections to make for a Benes network shuffle layer on `2^k` inputs.  The result
/// is a map from output index to the input index that it receives a value from.
fn permute_shuffle_sequence(k: u8, flip: bool) -> Vec<u32> {
    debug_assert!(k >= 1);
    let mut v = Vec::with_capacity(1 << k);
    if !flip {
        for i in 0 .. 1 << (k - 1) {
            v.push(i * 2);
        }
        for i in 0 .. 1 << (k - 1) {
            v.push(i * 2 + 1);
        }
    } else {
        for i in  0 .. 1 << k {
            v.push((i >> 1) | ((i & 1) << (k - 1)));
        }
    }
    v
}


#[derive(Clone, Debug)]
pub struct VecSink<IR: SieveIrFormat> {
    public_inputs: Vec<IR::PublicInputs>,
    private_inputs: Vec<IR::PrivateInputs>,
    relations: Vec<IR::Relation>,
}

impl<IR: SieveIrFormat> Default for VecSink<IR> {
    fn default() -> VecSink<IR> {
        VecSink {
            public_inputs: Vec::new(),
            private_inputs: Vec::new(),
            relations: Vec::new(),
        }
    }
}


impl<S: zki_sieve::Sink> Dispatch for SieveIrFunctionSink<S, SieveIrV1> {
    fn flush(&mut self, free_all_pages: bool) {
        use zki_sieve_v3::structs::IR_VERSION;
        use zki_sieve::structs::gates::Gate;
        use zki_sieve::structs::header::Header;
        use zki_sieve::structs::relation::{Relation, BOOL, FUNCTION};
        use zki_sieve::structs::witness::Witness;

        // There are no `@new` gates in IR0/IR1, so we don't need to process `AllocPage`s.
        let _ = self.alloc.flush();

        if free_all_pages {
            for free in self.alloc.take_frees() {
                if free.start != free.end {
                    self.gates.push(Gate::Free(free.start, Some(free.end - 1)));
                }
            }
        }

        let functions = mem::take(&mut self.functions);
        let gates = mem::take(&mut self.gates);

        // Build and emit the messages
        let header = Header {
            version: IR_VERSION.to_string(),
            field_characteristic: vec![2],
            field_degree: 1,
        };
        let r = Relation {
            header: header.clone(),
            gate_mask: BOOL,
            feat_mask: FUNCTION,
            functions,
            gates,
        };
        self.sink.push_relation_message(&r).unwrap();
        self.emitted_relation = true;

        if self.private_bits.len() > 0 {
            let short_witness = mem::take(&mut self.private_bits).into_iter()
                .map(|b| vec![b as u8]).collect();
            let w = Witness {
                header,
                short_witness,
            };
            self.sink.push_witness_message(&w).unwrap();
        }
    }
}

impl<S: zki_sieve_v3::Sink> SieveIrFunctionSink<S, SieveIrV2> {
    fn emit_sieve_v2(&mut self, directives: Vec<zki_sieve_v3::structs::directives::Directive>) {
        use zki_sieve_v3::structs::IR_VERSION;
        use zki_sieve_v3::structs::public_inputs::PublicInputs;
        use zki_sieve_v3::structs::relation::Relation;
        use zki_sieve_v3::structs::types::Type;

        // Build and emit the messages
        let mut r = Relation {
            version: IR_VERSION.to_string(),
            plugins: Vec::new(),
            types: Vec::new(),
            conversions: Vec::new(),
            directives,
        };
        if !self.emitted_relation {
            if self.use_plugin_mux_v0 {
                r.plugins.push("mux_v0".into());
            }
            if self.use_plugin_permutation_check_v1 {
                r.plugins.push("permutation_check_v1".into());
            }
            if self.use_plugin_disjunction_v0 {
                r.plugins.push(SWITCH_PLUGIN_NAME.into());
            }
            r.types = vec![Type::Field(vec![2])];

            // Ensure every circuit contains at least one public input message.
            let p = PublicInputs {
                version: IR_VERSION.to_string(),
                type_value: Type::Field(vec![2]),
                inputs: vec![],
            };
            self.sink.push_public_inputs_message(&p).unwrap();
        }
        self.sink.push_relation_message(&r).unwrap();
        self.emitted_relation = true;
    }
}

impl<S: zki_sieve_v3::Sink> Dispatch for SieveIrFunctionSink<S, SieveIrV2> {
    fn flush(&mut self, free_all_pages: bool) {
        use zki_sieve_v3::structs::IR_VERSION;
        use zki_sieve_v3::structs::directives::Directive;
        use zki_sieve_v3::structs::function::FunctionBody;
        use zki_sieve_v3::structs::gates::Gate;
        use zki_sieve_v3::structs::private_inputs::PrivateInputs;
        use zki_sieve_v3::structs::types::Type;


        // Flush functions first.  Function definitions can always be moved earlier relative to
        // gates, so we do these first to make it easier to break up the function definitions into
        // separate messages if needed.
        let functions = mem::take(&mut self.functions);
        if functions.len() > 0 {
            let mut directives = Vec::with_capacity(functions.len());
            let mut total_gates = 0;
            let mut emit_directive = |d, len| {
                if directives.len() > 0 && total_gates + len > GATE_PAGE_SIZE {
                    self.emit_sieve_v2(mem::take(&mut directives));
                    total_gates = 0;
                }
                directives.push(d);
                total_gates += len;
            };

            for function in functions {
                let len = match function.body {
                    FunctionBody::Gates(ref gates) => gates.len(),
                    // We give `PluginBody` a positive cost to bound the number that can be placed
                    // in a single message.
                    FunctionBody::PluginBody(_) => 1,
                };
                if len > GATE_PAGE_SIZE {
                    eprintln!("warning: big function: {:?} has {} gates", function.name, len);
                }
                emit_directive(Directive::Function(function), len);
            }
            if directives.len() > 0 {
                self.emit_sieve_v2(directives);
            }
        }


        let allocs = self.alloc.flush();

        if free_all_pages {
            for free in self.alloc.take_frees() {
                if free.start != free.end {
                    self.gates.push(Gate::Delete(0, free.start, free.end - 1));
                }
            }
        }

        let mut directives = Vec::with_capacity(self.gates.len() + allocs.len());
        let mut iter = mem::take(&mut self.gates).into_iter();
        let mut prev = 0;
        for alloc in allocs {
            let n = alloc.pos - prev;
            directives.extend(iter.by_ref().take(n).map(|g| Directive::Gate(g)));
            prev = alloc.pos;

            if alloc.start != alloc.end {
                directives.push(Directive::Gate(Gate::New(0, alloc.start, alloc.end - 1)));
            }
        }
        directives.extend(iter.map(|g| Directive::Gate(g)));

        let mut directives_iter = directives.into_iter();
        loop {
            let chunk_directives =
                directives_iter.by_ref().take(GATE_PAGE_SIZE).collect::<Vec<_>>();
            if chunk_directives.len() == 0 {
                break;
            }
            self.emit_sieve_v2(chunk_directives);
        }

        if self.private_bits.len() > 0 {
            let mut private_bits_iter = mem::take(&mut self.private_bits).into_iter();
            loop {
                let chunk_inputs = private_bits_iter.by_ref().take(GATE_PAGE_SIZE)
                    .map(|b| vec![b as u8])
                    .collect::<Vec<_>>();
                if chunk_inputs.len() == 0 {
                    break;
                }
                let p = PrivateInputs {
                    version: IR_VERSION.to_string(),
                    type_value: Type::Field(vec![2]),
                    inputs: chunk_inputs,
                };
                self.sink.push_private_inputs_message(&p).unwrap();
            }
        }
    }
}

impl<S: zki_sieve_v5::Sink> SieveIrFunctionSink<S, SieveIrV3> {
    fn emit_sieve_v3(&mut self, directives: Vec<zki_sieve_v5::structs::directives::Directive>) {
        use zki_sieve_v5::structs::IR_VERSION;
        use zki_sieve_v5::structs::public_inputs::PublicInputs;
        use zki_sieve_v5::structs::relation::Relation;
        use zki_sieve_v5::structs::types::Type;

        // Build and emit the messages
        let mut r = Relation {
            version: IR_VERSION.to_string(),
            plugins: Vec::new(),
            types: Vec::new(),
            conversions: Vec::new(),
            directives,
        };
        if !self.emitted_relation {
            if self.use_plugin_mux_v0 {
                r.plugins.push("mux_v0".into());
            }
            if self.use_plugin_permutation_check_v1 {
                r.plugins.push("permutation_check_v1".into());
            }
            if self.use_plugin_disjunction_v0 {
                r.plugins.push(SWITCH_PLUGIN_NAME.into());
            }
            r.types = vec![Type::Field(vec![2])];

            // Ensure every circuit contains at least one public input message.
            let p = PublicInputs {
                version: IR_VERSION.to_string(),
                type_value: Type::Field(vec![2]),
                inputs: vec![],
            };
            self.sink.push_public_inputs_message(&p).unwrap();
        }
        self.sink.push_relation_message(&r).unwrap();
        self.emitted_relation = true;
    }
}

impl<S: zki_sieve_v5::Sink> Dispatch for SieveIrFunctionSink<S, SieveIrV3> {
    fn flush(&mut self, free_all_pages: bool) {
        use zki_sieve_v5::structs::IR_VERSION;
        use zki_sieve_v5::structs::directives::Directive;
        use zki_sieve_v5::structs::function::FunctionBody;
        use zki_sieve_v5::structs::gates::Gate;
        use zki_sieve_v5::structs::private_inputs::PrivateInputs;
        use zki_sieve_v5::structs::types::Type;


        // Flush functions first.  Function definitions can always be moved earlier relative to
        // gates, so we do these first to make it easier to break up the function definitions into
        // separate messages if needed.
        let functions = mem::take(&mut self.functions);
        if functions.len() > 0 {
            let mut directives = Vec::with_capacity(functions.len());
            let mut total_gates = 0;
            let mut emit_directive = |d, len| {
                if directives.len() > 0 && total_gates + len > GATE_PAGE_SIZE {
                    self.emit_sieve_v3(mem::take(&mut directives));
                    total_gates = 0;
                }
                directives.push(d);
                total_gates += len;
            };

            for function in functions {
                let len = match function.body {
                    FunctionBody::Gates(ref gates) => gates.len(),
                    // We give `PluginBody` a positive cost to bound the number that can be placed
                    // in a single message.
                    FunctionBody::PluginBody(_) => 1,
                };
                if len > GATE_PAGE_SIZE {
                    eprintln!("warning: big function: {:?} has {} gates", function.name, len);
                }
                emit_directive(Directive::Function(function), len);
            }
            if directives.len() > 0 {
                self.emit_sieve_v3(directives);
            }
        }


        let allocs = self.alloc.flush();

        if free_all_pages {
            for free in self.alloc.take_frees() {
                if free.start != free.end {
                    self.gates.push(Gate::Delete(0, free.start, free.end - 1));
                }
            }
        }

        let mut directives = Vec::with_capacity(self.gates.len() + allocs.len());
        let mut iter = mem::take(&mut self.gates).into_iter();
        let mut prev = 0;
        for alloc in allocs {
            let n = alloc.pos - prev;
            directives.extend(iter.by_ref().take(n).map(|g| Directive::Gate(g)));
            prev = alloc.pos;

            if alloc.start != alloc.end {
                directives.push(Directive::Gate(Gate::New(0, alloc.start, alloc.end - 1)));
            }
        }
        directives.extend(iter.map(|g| Directive::Gate(g)));

        let mut directives_iter = directives.into_iter();
        loop {
            let chunk_directives =
                directives_iter.by_ref().take(GATE_PAGE_SIZE).collect::<Vec<_>>();
            if chunk_directives.len() == 0 {
                break;
            }
            self.emit_sieve_v3(chunk_directives);
        }

        if self.private_bits.len() > 0 {
            let mut private_bits_iter = mem::take(&mut self.private_bits).into_iter();
            loop {
                let chunk_inputs = private_bits_iter.by_ref().take(GATE_PAGE_SIZE)
                    .map(|b| vec![b as u8])
                    .collect::<Vec<_>>();
                if chunk_inputs.len() == 0 {
                    break;
                }
                let p = PrivateInputs {
                    version: IR_VERSION.to_string(),
                    type_value: Type::Field(vec![2]),
                    inputs: chunk_inputs,
                };
                self.sink.push_private_inputs_message(&p).unwrap();
            }
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_shuffle_sequence_flip() {
        for k in 2 .. 6 {
            let fwd = permute_shuffle_sequence(k, false);
            let rev = permute_shuffle_sequence(k, true);
            assert_eq!(fwd.len(), 1 << k);
            assert_eq!(rev.len(), 1 << k);
            for i in 0 .. 1_u32 << k {
                assert!(fwd[i as usize] < 1 << k);
                assert!(rev[i as usize] < 1 << k);
                assert_eq!(fwd[rev[i as usize] as usize], i);
                assert_eq!(rev[fwd[i as usize] as usize], i);
            }
        }
    }

    #[test]
    fn test_shuffle_sequence_matches_benes_network() {
        for k in 2 .. 6 {
            let bn = BenesNetwork::new(1 << k, 1 << k);
            let fwd = permute_shuffle_sequence(k, false);
            let rev = permute_shuffle_sequence(k, true);
            for i in 0 .. bn.layer_size {
                assert_eq!(bn.switch(1, i), [fwd[i * 2 + 0], fwd[i * 2 + 1]]);
                assert_eq!(bn.switch(bn.num_layers - 1, i), [rev[i * 2 + 0], rev[i * 2 + 1]]);
            }
        }
    }
}
