use zki_sieve::producers::builder::{Builder, BuildGate};
use zki_sieve::{WireId, Gate, Value};
use BuildGate::*;
use num_bigint::BigUint;
use ff::PrimeField;
use crate::back::sieve_ir::field::encode_scalar;
use zki_sieve::structs::assignment::Assignment;
use zki_sieve::producers::sink::MemorySink;


/// Extensions to the basic builder.
pub struct BuilderExt {
    b: Builder<MemorySink>,
    powers_of_two: Vec<WireId>,

    pub zero: WireId,
    pub one: WireId,
    pub neg_one: WireId,
}

impl BuilderExt {
    pub fn new<Scalar: PrimeField>(mut b: Builder<MemorySink>) -> BuilderExt {
        let zero = b.create_gate(Constant(vec![0]));
        let one = b.create_gate(Constant(vec![1]));

        let minus_one = Scalar::one().neg();
        let neg_one = b.create_gate(Constant(encode_scalar(&minus_one)));

        BuilderExt {
            b,
            zero,
            one,
            neg_one,
            powers_of_two: vec![],
        }
    }

    pub fn create_gate(&mut self, gate: BuildGate) -> WireId {
        self.b.create_gate(gate)
    }

    /// Return a wire representing constant 2^n.
    /// Cache the constant gates from 0 to n.
    pub fn power_of_two(&mut self, n: usize) -> WireId {
        while self.powers_of_two.len() <= n {
            let exponent = self.powers_of_two.len() as u32;
            let value = BigUint::from(2 as u32).pow(exponent);
            let wire = self.b.create_gate(
                Constant(value.to_bytes_le()));
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
        self.b.create_gate(
            Add(left, right))
    }

    pub fn sub(&mut self, left: WireId, right: WireId) -> WireId {
        let neg_right = self.neg(right);
        self.b.create_gate(
            Add(left, neg_right))
    }

    pub fn neg(&mut self, wire: WireId) -> WireId {
        self.b.create_gate(
            Mul(wire, self.neg_one))
    }

    pub fn mul(&mut self, left: WireId, right: WireId) -> WireId {
        self.b.create_gate(
            Mul(left, right))
    }

    pub fn gates(&self) -> Vec<Gate> {
        self.b.gates.clone()
    }

    pub fn finish(self) {
        self.b.finish();
    }
}
