use crate::back::sieve_ir::field::encode_scalar;
use ff::PrimeField;
use num_bigint::BigUint;
use zki_sieve::producers::sink::MemorySink;
use zki_sieve::{
    producers::builder::{BuildGate, Builder},
    Source,
};
use zki_sieve::{Gate, Value, WireId};
use BuildGate::*;

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

    pub fn finish(self) -> MemorySink {
        self.b.finish()
    }

    fn get_gates(self) -> (Vec<Value>, Vec<Gate>) {
        let sink = self.finish();
        let source = Source::from_buffers(vec![
            sink.instance_buffer,
            sink.witness_buffer,
            sink.relation_buffer,
        ]);

        let mut witnesses = Vec::<Value>::new();
        let mut gates = Vec::<Gate>::new();

        source.iter_messages().for_each(|msg| match msg.unwrap() {
            zki_sieve::Message::Instance(_) => {}
            zki_sieve::Message::Witness(witness) => {
                let values = witness.short_witness.into_iter().map(|a| a.value);
                witnesses.extend(values);
            }
            zki_sieve::Message::Relation(rel) => {
                gates.extend_from_slice(&rel.gates);
            }
        });

        (witnesses, gates)
    }
}
