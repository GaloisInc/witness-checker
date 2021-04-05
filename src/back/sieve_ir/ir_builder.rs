use crate::back::sieve_ir::field::encode_field_order;
use crate::back::sieve_ir::field::encode_scalar;
use crate::back::sieve_ir::ir_cache::IRCache;
use crate::back::sieve_ir::ir_profiler::IRProfiler;
use ff::PrimeField;
use num_bigint::BigUint;
use zki_sieve::producers::builder::{BuildGate, GateBuilder, GateBuilderT};
use zki_sieve::Header;
use zki_sieve::Sink;
use zki_sieve::{Value, WireId};
use BuildGate::*;

/// Extensions to the basic builder.
pub struct IRBuilder<S: Sink> {
    pub b: IRCache<S>,
    pub prof: IRProfiler,

    pub zero: WireId,
    pub one: WireId,
    pub neg_one: WireId,
    powers_of_two: Vec<WireId>,
}

impl<S: Sink> GateBuilderT for IRBuilder<S> {
    fn create_gate(&mut self, gate: BuildGate) -> WireId {
        self.prof.notify_gate(&gate);
        self.b.create_gate(gate)
    }
}

impl<S: Sink> IRBuilder<S> {
    pub fn new<Scalar: PrimeField>(sink: S) -> Self {
        let field_order = encode_field_order::<Scalar>();
        let header = Header::new(field_order);
        let builder = GateBuilder::new(sink, header);
        let cached_builder = IRCache::new(builder);

        let mut irb = IRBuilder {
            b: cached_builder,
            prof: IRProfiler::default(),
            zero: 0,
            one: 0,
            neg_one: 0,
            powers_of_two: vec![],
        };

        irb.zero = irb.create_gate(Constant(vec![0]));
        irb.one = irb.create_gate(Constant(vec![1]));
        irb.neg_one = irb.create_gate(Constant(encode_scalar(&Scalar::one().neg())));
        irb.powers_of_two.push(irb.one);

        irb
    }

    /// Return a wire representing constant 2^n.
    /// Cache the constant gates from 0 to n.
    pub fn power_of_two(&mut self, n: usize) -> WireId {
        while self.powers_of_two.len() <= n {
            let exponent = self.powers_of_two.len() as u32;
            let value = BigUint::from(2 as u32).pow(exponent);
            let wire = self.create_gate(Constant(value.to_bytes_le()));
            self.powers_of_two.push(wire);
        }

        return self.powers_of_two[n];
    }

    pub fn new_constant(&mut self, value: Value) -> WireId {
        self.create_gate(Constant(value))
    }

    pub fn new_witness(&mut self, value: Option<Value>) -> WireId {
        self.create_gate(Witness(value))
    }

    pub fn assert_zero(&mut self, wire: WireId) {
        self.create_gate(AssertZero(wire));
    }

    pub fn add(&mut self, left: WireId, right: WireId) -> WireId {
        self.create_gate(Add(left, right))
    }

    pub fn sub(&mut self, left: WireId, right: WireId) -> WireId {
        let neg_right = self.neg(right);
        self.create_gate(Add(left, neg_right))
    }

    pub fn neg(&mut self, wire: WireId) -> WireId {
        self.create_gate(Mul(wire, self.neg_one))
    }

    pub fn mul(&mut self, left: WireId, right: WireId) -> WireId {
        self.create_gate(Mul(left, right))
    }

    pub fn finish(self) -> S {
        self.b.finish()
    }
}
