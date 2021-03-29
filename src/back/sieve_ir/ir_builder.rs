use crate::back::sieve_ir::field::encode_field_order;
use crate::back::sieve_ir::field::encode_scalar;
use ff::PrimeField;
use num_bigint::BigUint;
use zki_sieve::producers::builder::{BuildGate, GateBuilder};
use zki_sieve::Header;
use zki_sieve::Sink;
use zki_sieve::{Value, WireId};
use BuildGate::*;

/// Extensions to the basic builder.
pub struct IRBuilder<S: Sink> {
    b: GateBuilder<S>,
    powers_of_two: Vec<WireId>,

    pub zero: WireId,
    pub one: WireId,
    pub neg_one: WireId,
}

impl<S: Sink> IRBuilder<S> {
    pub fn new<Scalar: PrimeField>(sink: S) -> Self {
        let field_order = encode_field_order::<Scalar>();
        let mut b = GateBuilder::new(sink, Header::new(field_order));

        let zero = b.create_gate(Constant(vec![0]));
        let one = b.create_gate(Constant(vec![1]));
        let neg_one = b.create_gate(Constant(encode_scalar(&Scalar::one().neg())));

        IRBuilder {
            b,
            zero,
            one,
            neg_one,
            powers_of_two: vec![],
        }
    }

    /// Return a wire representing constant 2^n.
    /// Cache the constant gates from 0 to n.
    pub fn power_of_two(&mut self, n: usize) -> WireId {
        while self.powers_of_two.len() <= n {
            let exponent = self.powers_of_two.len() as u32;
            let value = BigUint::from(2 as u32).pow(exponent);
            let wire = self.b.create_gate(Constant(value.to_bytes_le()));
            self.powers_of_two.push(wire);
        }

        return self.powers_of_two[n];
    }

    pub fn new_constant(&mut self, value: Value) -> WireId {
        self.b.create_gate(Constant(value))
    }

    pub fn new_witness(&mut self, value: Option<Value>) -> WireId {
        self.b.create_gate(Witness(value))
    }

    pub fn assert_zero(&mut self, wire: WireId) {
        self.b.create_gate(AssertZero(wire));
    }

    pub fn add(&mut self, left: WireId, right: WireId) -> WireId {
        self.b.create_gate(Add(left, right))
    }

    pub fn sub(&mut self, left: WireId, right: WireId) -> WireId {
        let neg_right = self.neg(right);
        self.b.create_gate(Add(left, neg_right))
    }

    pub fn neg(&mut self, wire: WireId) -> WireId {
        self.b.create_gate(Mul(wire, self.neg_one))
    }

    pub fn mul(&mut self, left: WireId, right: WireId) -> WireId {
        self.b.create_gate(Mul(left, right))
    }

    pub fn finish(self) -> S {
        self.b.finish()
    }
}
