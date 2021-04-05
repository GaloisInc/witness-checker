use crate::back::sieve_ir::field::encode_field_order;
use crate::back::sieve_ir::field::encode_scalar;
use crate::back::sieve_ir::ir_dedup::IRDedup;
use crate::back::sieve_ir::ir_profiler::IRProfiler;
use ff::PrimeField;
use num_bigint::BigUint;
use zki_sieve::producers::builder::{BuildGate, GateBuilder, GateBuilderT};
use zki_sieve::Header;
use zki_sieve::Sink;
use zki_sieve::{Value, WireId};
use BuildGate::*;

pub trait IRBuilderT: GateBuilderT {
    fn zero(&self) -> WireId {
        0
    }
    fn one(&self) -> WireId {
        1
    }
    fn neg_one(&self) -> WireId {
        2
    }

    fn new_constant(&mut self, value: Value) -> WireId {
        self.create_gate(Constant(value))
    }

    fn new_witness(&mut self, value: Option<Value>) -> WireId {
        self.create_gate(Witness(value))
    }

    fn assert_zero(&mut self, wire: WireId) {
        self.create_gate(AssertZero(wire));
    }

    fn add(&mut self, left: WireId, right: WireId) -> WireId {
        self.create_gate(Add(left, right))
    }

    fn sub(&mut self, left: WireId, right: WireId) -> WireId {
        let neg_right = self.neg(right);
        self.create_gate(Add(left, neg_right))
    }

    fn neg(&mut self, wire: WireId) -> WireId {
        self.create_gate(Mul(wire, self.neg_one()))
    }

    fn mul(&mut self, left: WireId, right: WireId) -> WireId {
        self.create_gate(Mul(left, right))
    }

    fn power_of_two(&mut self, n: usize) -> WireId;

    /// Give a name to the current context for diagnostics. Multiple calls create a hierarchy of annotations.
    fn annotate(&mut self, _note: &str) {}

    /// Exit the last context that was started with annotate().
    fn deannotate(&mut self) {}
}

/// Extensions to the basic builder.
pub struct IRBuilder<S: Sink> {
    gate_builder: GateBuilder<S>,

    /// If dedup is enabled, gates will be deduplicated. Default: enabled.
    pub dedup: Option<IRDedup>,

    /// If profiler is enabled, it will track duplicate gates. Default: disabled.
    pub prof: Option<IRProfiler>,

    powers_of_two: Vec<WireId>,
}

impl<S: Sink> GateBuilderT for IRBuilder<S> {
    fn create_gate(&mut self, gate: BuildGate) -> WireId {
        let b = &mut self.gate_builder;

        if let Some(prof) = &mut self.prof {
            prof.notify_gate(&gate);
        }

        if let Some(dedup) = &mut self.dedup {
            dedup.create_gate(b, gate)
        } else {
            b.create_gate(gate)
        }
    }
}

impl<S: Sink> IRBuilderT for IRBuilder<S> {
    /// Return a wire representing constant 2^n.
    /// Cache the constant gates from 0 to n.
    fn power_of_two(&mut self, n: usize) -> WireId {
        while self.powers_of_two.len() <= n {
            let exponent = self.powers_of_two.len() as u32;
            let value = BigUint::from(2 as u32).pow(exponent);
            let wire = self.create_gate(Constant(value.to_bytes_le()));
            self.powers_of_two.push(wire);
        }

        return self.powers_of_two[n];
    }

    fn annotate(&mut self, note: &str) {
        if let Some(prof) = &mut self.prof {
            prof.annotate(note);
        }
    }

    fn deannotate(&mut self) {
        if let Some(prof) = &mut self.prof {
            prof.deannotate();
        }
    }
}

impl<S: Sink> IRBuilder<S> {
    /// Must call finish().
    pub fn new<Scalar: PrimeField>(sink: S) -> Self {
        let field_order = encode_field_order::<Scalar>();
        let header = Header::new(field_order);

        let mut irb = IRBuilder {
            gate_builder: GateBuilder::new(sink, header),
            dedup: Some(IRDedup::default()),
            prof: None, // Some(IRProfiler::default()),
            powers_of_two: vec![],
        };

        let zero = irb.create_gate(Constant(vec![0]));
        assert_eq!(zero, irb.zero());
        let one = irb.create_gate(Constant(vec![1]));
        assert_eq!(one, irb.one());
        let neg_one = irb.create_gate(Constant(encode_scalar(&Scalar::one().neg())));
        assert_eq!(neg_one, irb.neg_one());
        irb.powers_of_two.push(irb.one());

        irb
    }

    pub fn finish(self) -> S {
        self.gate_builder.finish()
    }

    pub fn disable_dedup(&mut self) {
        self.dedup = None;
    }

    pub fn enable_profiler(&mut self) {
        self.prof = Some(IRProfiler::default());
    }
}
