use crate::back::sieve_ir::field::encode_field_order;
use crate::back::sieve_ir::field::encode_scalar;
use crate::back::sieve_ir::ir_dedup::IRDedup;
use crate::back::sieve_ir::ir_profiler::IRProfiler;
use ff::PrimeField;
use num_bigint::BigUint;
use zki_sieve::producers::builder::{BuildGate, GateBuilder, GateBuilderT};
use zki_sieve::{Header, WireId};
use zki_sieve::Sink;
use zki_sieve::{Value};
use BuildGate::*;
use std::rc::{Rc, Weak};
use std::fmt;
use zki_sieve::producers::build_gates::NO_OUTPUT;
use std::ops::Deref;

#[derive(Clone)]
pub struct IRWire {
    wire: Rc<WireId>,
    builder: Weak<dyn GateBuilderT>,
}

impl Drop for IRWire {

    /// Destructor for IRWire. Once there is no more reference to this
    /// wire, it's automatically freed, and the corresponding 'Free' gate
    /// is appended to the IR circuit.
    fn drop(&mut self) {
        // If this is the last living reference to this wire, then automatically
        // append a Free gate to the circuit.
        if Rc::strong_count(&self.wire) == 1 {
            match self.builder.upgrade() {
                Some(b) => {
                    if *self.wire != NO_OUTPUT {
                        b.create_gate(BuildGate::Free(*self.wire, None));
                    }
                }
                None => {},
            }
        }
    }
}

impl PartialEq<IRWire> for IRWire {
    fn eq(&self, other: &IRWire) -> bool {
        *self.wire == *other.wire
    }
}

impl IRWire {
    pub fn new(wire: WireId, builder: Weak<dyn GateBuilderT>) -> Self {
        IRWire {
            wire: Rc::new(wire),
            builder,
        }
    }

    pub fn wire(&self) -> WireId {
        *self.wire
    }
}

pub trait IRBuilderT {
    fn zero(&self) -> IRWire;
    fn one(&self) -> IRWire;
    fn neg_one(&self) -> IRWire;

    fn create_gate(&mut self, gate: BuildGate) -> IRWire;

    fn new_constant(&mut self, value: Value) -> IRWire {
        self.create_gate(Constant(value))
    }

    fn new_witness(&mut self, value: Option<Value>) -> IRWire {
        self.create_gate(Witness(value))
    }

    fn assert_zero(&mut self, wire: IRWire) {
        self.create_gate(AssertZero(wire.wire()));
    }

    fn add(&mut self, left: IRWire, right: IRWire) -> IRWire {
        self.create_gate(Add(left.wire(), right.wire()))
    }

    fn sub(&mut self, left: IRWire, right: IRWire) -> IRWire {
        let neg_right = self.neg(right);
        self.create_gate(Add(left.wire(), neg_right.wire()))
    }

    fn neg(&mut self, wire: IRWire) -> IRWire {
        self.create_gate(Mul(wire.wire(), self.neg_one().wire()))
    }

    fn mul(&mut self, left: IRWire, right: IRWire) -> IRWire {
        self.create_gate(Mul(left.wire(), right.wire()))
    }

    fn power_of_two(&mut self, n: usize) -> IRWire;

    /// Give a name to the current context for diagnostics. Multiple calls create a hierarchy of annotations.
    fn annotate(&mut self, _note: &str) {}

    /// Exit the last context that was started with annotate().
    fn deannotate(&mut self) {}
}

/// Extensions to the basic builder.
pub struct IRBuilder<S: Sink> {
    gate_builder: Rc<GateBuilder<S>>,

    /// If dedup is enabled, gates will be deduplicated. Default: enabled.
    /// This affects the resulting relation.
    pub dedup: Option<IRDedup>,

    /// If profiler is enabled, it will track duplicate gates. Default: disabled.
    pub prof: Option<IRProfiler>,

    zero: Option<IRWire>,
    one: Option<IRWire>,
    neg_one: Option<IRWire>,
    powers_of_two: Vec<IRWire>,
}

impl<S: 'static + Sink> IRBuilderT for IRBuilder<S> {
    fn zero(&self) -> IRWire {
        self.zero.as_ref().unwrap().clone()
    }

    fn one(&self) -> IRWire {
        self.one.as_ref().unwrap().clone()
    }

    fn neg_one(&self) -> IRWire {
        self.neg_one.as_ref().unwrap().clone()
    }

    fn create_gate(&mut self, gate: BuildGate) -> IRWire {

        if let Some(prof) = &mut self.prof {
            prof.notify_gate(&gate);
        }

        let b = Rc::downgrade(&self.gate_builder);
        if let Some(dedup) = &mut self.dedup {
            dedup.create_gate(self.gate_builder.clone(), gate)
        } else {
            IRWire:: new (
                self.gate_builder.create_gate(gate),
                b
            )
        }
    }

    /// Return a wire representing constant 2^n.
    /// Cache the constant gates from 0 to n.
    fn power_of_two(&mut self, n: usize) -> IRWire {
        while self.powers_of_two.len() <= n {
            let exponent = self.powers_of_two.len() as u32;
            let value = BigUint::from(2 as u32).pow(exponent);
            let wire = self.create_gate(Constant(value.to_bytes_le()));
            self.powers_of_two.push(wire);
        }

        return self.powers_of_two[n].clone();
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

impl<S: 'static + Sink> IRBuilder<S> {
    /// Must call finish().
    pub fn new<Scalar: PrimeField>(sink: S) -> Self {
        let field_order = encode_field_order::<Scalar>();
        let header = Header::new(field_order);

        let mut irb = IRBuilder {
            gate_builder: Rc::new(GateBuilder::new(sink, header)),
            dedup: Some(IRDedup::default()),
            prof: None, // Some(IRProfiler::default()),
            zero: None,
            one: None,
            neg_one: None,
            powers_of_two: vec![],
        };

        irb.zero = Some(irb.create_gate(Constant(vec![0])));
        // assert_eq!(irb.zero, irb.zero());
        irb.one = Some(irb.create_gate(Constant(vec![1])));
        // assert_eq!(irb.one, irb.one());
        irb.neg_one = Some(irb.create_gate(Constant(encode_scalar(&Scalar::one().neg()))));
        // assert_eq!(irb.neg_one, irb.neg_one());
        irb.powers_of_two.push(irb.one());

        irb
    }

    pub fn finish(self) -> S {
        if let Some(dedup) = self.dedup {
            // clean-up the potential IRWire kept in the memory of the deduplicator.
            drop(dedup);
        }
        drop(self.zero);
        drop(self.one);
        drop(self.powers_of_two);

        // We can use Rc::try_unwrap() here since we ensures that self.gate_builder is never cloned,
        // so no other Rc<GateBuilder> will exist. And this will never enter the panic!()
        let b = Rc::try_unwrap(self.gate_builder).unwrap_or_else(|_| panic!("Another reference to the GateBuilder exists elsewhere, while it should not!"));
        b.finish()
    }

    pub fn disable_dedup(&mut self) {
        self.dedup = None;
    }

    pub fn enable_profiler(&mut self) {
        self.prof = Some(IRProfiler::default());
    }
}
