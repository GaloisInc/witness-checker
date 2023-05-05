use std::cmp::{self, Ordering};
use std::collections::{HashMap, BinaryHeap};
use std::convert::TryFrom;
use std::io;
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

    fn new_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        private_count: u64,
        gates: Vec<Self::Gate>,
    ) -> Self::Function;

    const HAS_PLUGINS: bool;
    fn new_plugin_function(
        name: String,
        outs: impl IntoIterator<Item = u64>,
        ins: impl IntoIterator<Item = u64>,
        plugin_name: String,
        op_name: String,
        args: Vec<String>,
    ) -> Self::Function;

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

    _marker: PhantomData<IR>,
}

pub type SieveIrV1Sink<S> = SieveIrFunctionSink<S, v1::SieveIrV1>;
pub type SieveIrV2Sink<S> = SieveIrFunctionSink<S, SieveIrV2>;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
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
}

impl FunctionDesc {
    pub fn name(self) -> String {
        match self {
            FunctionDesc::LitZero(n) => format!("lit_zero_{}", n),
            FunctionDesc::Private(n) => format!("private_{}", n),
            FunctionDesc::Copy(n) => format!("copy_{}", n),
            FunctionDesc::And(n) => format!("and_{}", n),
            FunctionDesc::Or(n) => format!("or_{}", n),
            FunctionDesc::Xor(n) => format!("xor_{}", n),
            FunctionDesc::Not(n) => format!("not_{}", n),
            FunctionDesc::Add(n) => format!("add_{}", n),
            FunctionDesc::AddNoWrap(n) => format!("add_no_wrap_{}", n),
            FunctionDesc::Sub(n) => format!("sub_{}", n),
            FunctionDesc::Mul(n) => format!("mul_{}", n),
            FunctionDesc::MulNoWrap(n) => format!("mul_no_wrap_{}", n),
            FunctionDesc::WideMul(n) => format!("wide_mul_{}", n),
            FunctionDesc::Neg(n) => format!("neg_{}", n),
            FunctionDesc::Mux(n) => format!("mux_{}", n),
            FunctionDesc::Permute(n, m) => format!("permute_{}_{}", n, m),
            FunctionDesc::PermuteLayerShuffle(n, m, l) =>
                format!("permute_layer_shuffle_{}_{}_{}", n, m, l),
            FunctionDesc::PermuteLayerSwitches(n, m, l) =>
                format!("permute_layer_switches_{}_{}_{}", n, m, l),
            FunctionDesc::PermuteSwitch(n) => format!("permute_switch_{}", n),
            FunctionDesc::PermuteSwitches(n, m) =>
                format!("permute_switches_{}_{}", n, m),
            FunctionDesc::PermuteSwitchPublic(n, swap) =>
                format!("permute_switch_public_{}_{}", n, swap as u8),
            FunctionDesc::PermuteShuffle(n, k, flip) =>
                format!("permute_shuffle_{}_{}_{}", n, k, flip as u8),
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

    fn sig(&self) -> (&[u64], &[u64]) {
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

    fn lit_zero_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(IR::gate_constant(out + i, vec![0]));
        }
    }

    fn lit_one_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(IR::gate_constant(out + i, vec![1]));
        }
    }

    fn private_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(IR::gate_private(out + i));
        }
    }

    fn copy_into(&mut self, out: WireId, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_copy(out + i, a + i));
        }
    }

    fn and_into(&mut self, out: WireId, n: u64, a: WireId, b: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_and(out + i, a + i, b + i));
        }
    }

    fn xor_into(&mut self, out: WireId, n: u64, a: WireId, b: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_xor(out + i, a + i, b + i));
        }
    }

    fn not_into(&mut self, out: WireId, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(IR::gate_not(out + i, a + i));
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
        assert_eq!(zki_sink.public_inputs.len(), 0);
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
        self.func_map.insert(desc, idx);
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
                        name.clone(),
                        [n],
                        [1, n, n],
                        "mux_v0".into(),
                        "strict".into(),
                        vec![],
                    ));
                    return idx;
                },

                _ => {},
            }
        }

        let mut sub_sink = self.sub_sink();

        let mut private_count = 0;
        let (output_count, input_count) = match desc {
            FunctionDesc::LitZero(n) => {
                let [out] = sub_sink.alloc.preallocate([n]);
                sub_sink.lit_zero_into(out, n);
                (vec![n], vec![])
            },

            FunctionDesc::Private(n) => {
                let [out] = sub_sink.alloc.preallocate([n]);
                sub_sink.private_into(out, n);
                private_count = n;
                (vec![n], vec![])
            },

            FunctionDesc::Copy(n) => {
                let [out, a] = sub_sink.alloc.preallocate([n, n]);
                sub_sink.copy_into(out, n, a);
                (vec![n], vec![n])
            },

            FunctionDesc::And(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                sub_sink.and_into(out, n, a, b);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Or(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let a_inv = sub_sink.not(TEMP, n, a);
                let b_inv = sub_sink.not(TEMP, n, b);
                let ab_inv = sub_sink.and(TEMP, n, a_inv, b_inv);
                sub_sink.not_into(out, n, ab_inv);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Xor(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                sub_sink.xor_into(out, n, a, b);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Not(n) => {
                let [out, a] = sub_sink.alloc.preallocate([n, n]);
                sub_sink.not_into(out, n, a);
                (vec![n], vec![n])
            },

            FunctionDesc::Add(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::add(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::No);
                sub_sink.copy_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::AddNoWrap(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::add(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::Yes);
                sub_sink.copy_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Sub(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::sub(&mut sub_sink, TEMP, n, a, b);
                sub_sink.copy_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::Mul(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::mul(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::No);
                sub_sink.copy_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::MulNoWrap(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([n, n, n]);
                let ab = arith::mul(&mut sub_sink, TEMP, n, a, b, AssertNoWrap::Yes);
                sub_sink.copy_into(out, n, ab);
                (vec![n], vec![n, n])
            },
            FunctionDesc::WideMul(n) => {
                let [out, a, b] = sub_sink.alloc.preallocate([2 * n, n, n]);
                let ab = arith::wide_mul(&mut sub_sink, TEMP, n, a, b);
                sub_sink.copy_into(out, 2 * n, ab);
                (vec![2 * n], vec![n, n])
            },
            FunctionDesc::Neg(n) => {
                let [out, a] = sub_sink.alloc.preallocate([n, n]);
                let a_neg = arith::neg(&mut sub_sink, TEMP, n, a);
                sub_sink.copy_into(out, n, a_neg);
                (vec![n], vec![n])
            },
            FunctionDesc::Mux(n) => {
                // Note the order of the `e` and `t` arguments is reversed, for compatibility with
                // the `mux_v0` plugin.
                let [out, c, e, t] = sub_sink.alloc.preallocate([n, 1, n, n]);
                let mux = ops::mux(&mut sub_sink, TEMP, n, c, t, e);
                sub_sink.copy_into(out, n, mux);
                (vec![n], vec![1, n, n])
            },

            FunctionDesc::Permute(n, m) => {
                sub_sink.permute_body(n, m)
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
                sub_sink.private_into(swap, 1);
                sub_sink.call_into(out, FunctionDesc::Mux(n), &[swap, inp, inp + n]);
                sub_sink.call_into(out + n, FunctionDesc::Mux(n), &[swap, inp + n, inp]);
                (vec![2 * n], vec![2 * n])
            },
            FunctionDesc::PermuteSwitches(n, m) => {
                let [out, inp] = sub_sink.alloc.preallocate([n * 2 * m as u64, n * 2 * m as u64]);
                if m <= 4 {
                    for i in 0 .. m as u64 {
                        sub_sink.call_into(
                            out + n * 2 * i,
                            FunctionDesc::PermuteSwitch(n),
                            &[inp + n * 2 * i],
                        );
                    }
                } else if m.is_power_of_two() {
                    sub_sink.call_into(
                        out,
                        FunctionDesc::PermuteSwitches(n, m / 2),
                        &[inp],
                    );
                    sub_sink.call_into(
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
                        sub_sink.call_into(
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
                    sub_sink.copy_into(out, n, inp + n);
                    sub_sink.copy_into(out + n, n, inp);
                } else {
                    sub_sink.copy_into(out, 2 * n, inp);
                }
                (vec![2 * n], vec![2 * n])
            },
            FunctionDesc::PermuteShuffle(n, k, flip) => {
                let [out, inp] = sub_sink.alloc.preallocate([n * (1 << k), n * (1 << k)]);
                let out_to_inp = permute_shuffle_sequence(k, flip);
                for (i, &j) in out_to_inp.iter().enumerate() {
                    sub_sink.call_into(
                        out + n * i as u64,
                        FunctionDesc::Copy(n),
                        &[inp + n * j as u64],
                    );
                }
                (vec![n * (1 << k)], vec![n * (1 << k)])
            },
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
                self.copy_into(out, n, inp);
                return (vec![n], vec![n]);
            },
            2 => {
                let [out, inp] = self.alloc.preallocate([2 * n, 2 * n]);
                self.call_into(out, FunctionDesc::PermuteSwitch(n), &[inp]);
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
        let mut cur = self.alloc_wires(TEMP, num_wires);
        self.call_into(cur, FunctionDesc::PermuteLayerShuffle(n, m, 0), &[inp]);

        // TODO: insert deletes between layers (use `expire`/`advance`?)
        for l in 0 .. bn.num_layers {
            if l > 0 {
                // Shuffle
                let next = self.alloc_wires(TEMP, num_wires);
                self.call_into(next, FunctionDesc::PermuteLayerShuffle(n, m, l), &[cur]);
                cur = next;
            }

            {
                // Switches
                let next = if l < bn.num_layers - 1 {
                    self.alloc_wires(TEMP, num_wires)
                } else {
                    // Outputs of the last switch layer go directly to the function outputs.
                    out
                };
                self.call_into(next, FunctionDesc::PermuteLayerSwitches(n, m, l), &[cur]);
                cur = next;
            }
        }

        (vec![n * m_rounded as u64], vec![n * m as u64])
    }

    fn permute_layer_shuffle(&mut self, n: u64, m: u32, l: usize) -> (Vec<u64>, Vec<u64>) {
        let mut bn = BenesNetwork::new(m, m);
        let m_rounded = 2 * bn.layer_size as u32;
        bn.set_routes(&[]);

        if l == 0 {
            let [out, inp] = self.alloc.preallocate([n * m_rounded as u64, n * m as u64]);

            // Pad out `inp` with zeros to reach `num_wires`.
            for i in 0 .. m as u64 {
                self.call_into(out + n * i, FunctionDesc::Copy(n), &[inp + n * i]);
            }
            for i in m as u64 .. m_rounded as u64 {
                self.call_into(out + n * i, FunctionDesc::LitZero(n), &[]);
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
                self.call_idx_into(
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

                self.call_into(
                    out + n * 2 * start as u64,
                    FunctionDesc::PermuteSwitches(n, (end - start) as u32),
                    &[inp + n * 2 * start as u64],
                );

            } else {
                let swap = flags.contains(benes::SwitchFlags::F_SWAP);
                self.call_into(
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
        self.call_idx_into(out, idx, args);
        out
    }

    fn call_into(
        &mut self,
        out: WireId,
        desc: FunctionDesc,
        args: &[WireId],
    ) {
        let idx = self.get_function(desc);
        self.call_idx_into(out, idx, args);
    }

    fn call_idx_into(
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
}

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
        self.emit_call(expire, FunctionDesc::Private(n), &[])
    }
    fn private_value(&mut self, n: u64, value: Bits) {
        for i in 0 .. n {
            self.private_bits.push(value.get(i as usize));
        }
    }
    fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Copy(n), &[a])
    }
    fn concat_chunks(&mut self, expire: Time, entries: &[(Source, u64)]) -> WireId {
        let total = entries.iter().map(|&(_, n)| n).sum();
        let w = self.alloc_wires(expire, total);
        let mut pos = 0;
        for &(source, n) in entries {
            match source {
                Source::Zero => {
                    self.lit_zero_into(w + pos, n);
                },
                Source::One => {
                    self.lit_one_into(w + pos, n);
                },
                Source::Wires(a) => {
                    self.copy_into(w + pos, n, a);
                },
                Source::RepWire(a) => {
                    for i in 0 .. n {
                        self.gates.push(IR::gate_copy(w + pos + i, a));
                    }
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
            let idx = sub_sink.get_function(FunctionDesc::Copy(return_n));
            let info = &sub_sink.func_info[idx];
            sub_sink.gates.push(IR::gate_call(
                info.name.clone(),
                iter::once((return_wire, return_wire + return_n - 1)),
                iter::once((out_wire, out_wire + return_n - 1)),
            ));
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
    fn permute_private_values(&mut self, num_items: u64, perm: Bits) {
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
        use zki_sieve::Sink;
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
        use zki_sieve_v3::Sink;
        use zki_sieve_v3::structs::IR_VERSION;
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
            r.types = vec![Type::Field(vec![2])];
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
                let mut p = PrivateInputs {
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
