use std::cmp::{self, Ordering};
use std::collections::{HashMap, BinaryHeap};
use std::convert::TryFrom;
use std::io;
use std::iter;
use std::mem;
use crate::ir::circuit::Bits;
use zki_sieve_v3::{self, Gate};
use zki_sieve_v3::structs::IR_VERSION;
use zki_sieve_v3::structs::count::Count;
use zki_sieve_v3::structs::directives::Directive;
use zki_sieve_v3::structs::function::{Function, FunctionBody};
use zki_sieve_v3::structs::private_inputs::PrivateInputs;
use zki_sieve_v3::structs::public_inputs::PublicInputs;
use zki_sieve_v3::structs::relation::Relation;
use zki_sieve_v3::structs::types::Type;
use zki_sieve_v3::structs::wirerange::WireRange;
use super::{Sink, WireId, Time, TEMP, Source};
use super::arith;
use super::wire_alloc::WireAlloc;


pub struct SieveIrV2Sink<S> {
    sink: S,
    alloc: WireAlloc,
    gates: Vec<Gate>,
    private_bits: Vec<bool>,
    /// Functions in `zki_sieve_v3` representation.  This vector is drained on `flush()`.
    functions: Vec<Function>,
    /// Info about function names and signatures.  This vector persists across `flush()`; it always
    /// contains all functions that have been declared so far.
    func_info: Vec<FunctionInfo>,
    func_map: HashMap<FunctionDesc, usize>,
    /// Whether we've emitted a relation message yet.  The first relation message must contain some
    /// additional data.
    emitted_relation: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
enum FunctionDesc {
    Copy(u64),
    And(u64),
    Or(u64),
    Xor(u64),
    Not(u64),
    Add(u64),
    Sub(u64),
    Mul(u64),
    WideMul(u64),
    Neg(u64),
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

const GATE_PAGE_SIZE: usize = 64 * 1024;

impl<S: zki_sieve_v3::Sink> SieveIrV2Sink<S> {
    pub fn new(sink: S) -> SieveIrV2Sink<S> {
        SieveIrV2Sink {
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
        }
    }

    pub fn finish(mut self) -> S {
        self.flush(true);
        self.sink
    }

    fn alloc_wires(&mut self, expire: Time, n: u64) -> WireId {
        self.alloc.alloc(expire, n, self.gates.len())
    }

    fn flush(&mut self, free_all_pages: bool) {
        use zki_sieve_v3::Sink;

        let allocs = self.alloc.flush();

        if free_all_pages {
            for free in self.alloc.take_frees() {
                if free.start != free.end {
                    self.gates.push(Gate::Delete(0, free.start, free.end - 1));
                }
            }
        }

        let mut directives = Vec::with_capacity(
            self.functions.len() + self.gates.len() + allocs.len());
        directives.extend(mem::take(&mut self.functions).into_iter().map(Directive::Function));
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

        // Build and emit the messages
        let mut r = Relation {
            version: IR_VERSION.to_string(),
            plugins: Vec::new(),
            types: Vec::new(),
            conversions: Vec::new(),
            directives,
        };
        if !self.emitted_relation {
            r.types = vec![Type::Field(vec![2])];
        }
        self.sink.push_relation_message(&r).unwrap();
        self.emitted_relation = true;

        if self.private_bits.len() > 0 {
            let inputs = mem::take(&mut self.private_bits).into_iter()
                .map(|b| vec![b as u8]).collect();
            let mut p = PrivateInputs {
                version: IR_VERSION.to_string(),
                type_value: Type::Field(vec![2]),
                inputs,
            };
            self.sink.push_private_inputs_message(&p).unwrap();
        }
    }

    fn lit_zero_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(Gate::Constant(0, out + i, vec![0]));
        }
    }

    fn lit_one_into(&mut self, out: WireId, n: u64) {
        for i in 0 .. n {
            self.gates.push(Gate::Constant(0, out + i, vec![1]));
        }
    }

    fn copy_into(&mut self, out: WireId, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::Copy(0, out + i, a + i));
        }
    }

    fn and_into(&mut self, out: WireId, n: u64, a: WireId, b: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::Mul(0, out + i, a + i, b + i));
        }
    }

    fn xor_into(&mut self, out: WireId, n: u64, a: WireId, b: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::Add(0, out + i, a + i, b + i));
        }
    }

    fn not_into(&mut self, out: WireId, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::AddConstant(0, out + i, a + i, vec![1]));
        }
    }

    fn get_function(
        &mut self,
        desc: FunctionDesc,
    ) -> usize {
        if let Some(s) = self.func_map.get(&desc) {
            return s.to_owned();
        }

        let mut sub_sink = SieveIrV2Sink {
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
        };

        let (output_count, input_count) = match desc {
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
                let ab = arith::add(&mut sub_sink, TEMP, n, a, b);
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
                let ab = arith::mul(&mut sub_sink, TEMP, n, a, b);
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
        };

        // Move `func_map` and `func_info` from `sub_sink` back into `self`, so in the future we
        // can use any extra functions that happened to be defined by this `sub_sink`.
        self.func_map = mem::take(&mut sub_sink.func_map);
        self.func_info = mem::take(&mut sub_sink.func_info);
        let idx = self.func_info.len();
        self.func_map.insert(desc, idx);
        let name = format!("f{}", idx);
        self.func_info.push(FunctionInfo {
            name: name.clone(),
            counts: output_count.iter().cloned().chain(input_count.iter().cloned()).collect(),
            num_outputs: output_count.len(),
        });

        // For functions with no outputs (e.g. `And(0)`), we record an entry in `self.func_info`
        // but don't emit an actual `zki_sieve_v3` function.
        if output_count.iter().cloned().sum::<u64>() == 0 {
            return idx;
        }

        let zki_sink = sub_sink.finish();
        assert_eq!(zki_sink.private_inputs.len(), 0);
        assert_eq!(zki_sink.public_inputs.len(), 0);
        let mut gates = Vec::with_capacity(
            zki_sink.relations.iter().map(|r| r.directives.len()).sum());
        for r in zki_sink.relations {
            debug_assert_eq!(r.plugins, Vec::<String>::new());
            debug_assert_eq!(r.types, vec![Type::Field(vec![2])]);
            for d in r.directives {
                match d {
                    Directive::Gate(g) => gates.push(g),
                    Directive::Function(f) => self.functions.push(f),
                }
            }
        }
        let mut f = Function {
            name: name.clone(),
            output_count: output_count.into_iter().map(|n| Count::new(0, n)).collect(),
            input_count: input_count.into_iter().map(|n| Count::new(0, n)).collect(),
            body: FunctionBody::Gates(gates),
        };
        self.functions.push(f);

        idx
    }

    fn emit_call(
        &mut self,
        expire: Time,
        desc: FunctionDesc,
        args: &[WireId],
    ) -> WireId {
        let idx = self.get_function(desc);
        let total_out = self.func_info[idx].outputs().iter().cloned().sum();
        if total_out == 0 {
            // Function has no outputs, so there's no need to emit a call, and we can just return a
            // dummy `WireId`.
            return 0;
        }
        let out = self.alloc_wires(expire, total_out);
        let info = &self.func_info[idx];

        debug_assert_eq!(args.len(), info.inputs().len());
        let mut inputs = Vec::with_capacity(info.inputs().len());
        for (&n, &w) in info.inputs().iter().zip(args.iter()) {
            inputs.push(WireRange::new(w, w + n - 1));
        }

        let mut outputs = Vec::with_capacity(info.outputs().len());
        let mut next_out = out;
        for &n in info.outputs() {
            outputs.push(WireRange::new(next_out, next_out + n - 1));
            next_out += n;
        }

        self.gates.push(Gate::Call(info.name.clone(), outputs, inputs));

        out
    }
}

impl<S: zki_sieve_v3::Sink> Sink for SieveIrV2Sink<S> {
    fn lit(&mut self, expire: Time, n: u64, bits: Bits) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            let bit = bits.get(i as usize);
            self.gates.push(Gate::Constant(0, w + i, vec![bit as u8]));
        }
        w
    }
    fn private(&mut self, expire: Time, n: u64, value: Option<Bits>) -> WireId {
        let w = self.alloc_wires(expire, n);
        for i in 0 .. n {
            self.gates.push(Gate::Private(0, w + i));
            if let Some(v) = value.as_ref() {
                self.private_bits.push(v.get(i as usize));
            }
        }
        w
    }
    fn copy(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        let w = self.alloc_wires(expire, n);
        self.copy_into(w, n, a);
        w
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
                        self.gates.push(Gate::Copy(0, w + pos + i, a));
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
    fn sub(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Sub(n), &[a, b])
    }
    fn mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Mul(n), &[a, b])
    }
    fn wide_mul(&mut self, expire: Time, n: u64, a: WireId, b: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::WideMul(n), &[a, b])
    }
    fn neg(&mut self, expire: Time, n: u64, a: WireId) -> WireId {
        self.emit_call(expire, FunctionDesc::Neg(n), &[a])
    }

    fn assert_zero(&mut self, n: u64, a: WireId) {
        for i in 0 .. n {
            self.gates.push(Gate::AssertZero(0, a + i));
        }
    }

    fn free_expired(&mut self, now: Time) {
        for free in self.alloc.advance(now) {
            if free.start != free.end {
                self.gates.push(Gate::Delete(0, free.start, free.end - 1));
            }
        }

        if self.gates.len() >= GATE_PAGE_SIZE {
            self.flush(false);
        }
    }
}


#[derive(Clone, Debug, Default)]
struct VecSink {
    public_inputs: Vec<zki_sieve_v3::PublicInputs>,
    private_inputs: Vec<zki_sieve_v3::PrivateInputs>,
    relations: Vec<zki_sieve_v3::Relation>,
}

impl zki_sieve_v3::Sink for VecSink {
    type Write = Vec<u8>;

    fn get_public_inputs_writer(
        &mut self,
        type_value: Type,
    ) -> zki_sieve_v3::Result<&mut Self::Write> {
        unimplemented!()
    }
    fn get_private_inputs_writer(
        &mut self,
        type_value: Type,
    ) -> zki_sieve_v3::Result<&mut Self::Write> {
        unimplemented!()
    }
    fn get_relation_writer(&mut self) -> &mut Self::Write {
        unimplemented!()
    }

    fn push_public_inputs_message(
        &mut self,
        public_inputs: &PublicInputs,
    ) -> zki_sieve_v3::Result<()> {
        self.public_inputs.push(public_inputs.clone());
        Ok(())
    }

    fn push_private_inputs_message(
        &mut self,
        private_inputs: &PrivateInputs,
    ) -> zki_sieve_v3::Result<()> {
        self.private_inputs.push(private_inputs.clone());
        Ok(())
    }

    fn push_relation_message(
        &mut self,
        relation: &Relation,
    ) -> zki_sieve_v3::Result<()> {
        self.relations.push(relation.clone());
        Ok(())
    }
}
