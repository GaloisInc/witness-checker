use crate::back::sieve_ir_v2::field::encode_scalar;
use crate::back::sieve_ir_v2::field::get_field_order;
use crate::back::sieve_ir_v2::ir_dedup::IRDedup;
use crate::back::sieve_ir_v2::ir_profiler::IRProfiler;
use ff::PrimeField;
use num_bigint::{BigUint, BigInt};
use num_integer::Integer;
use num_traits::{Zero, One};
use zki_sieve_v3::{WireId, Value, Sink};
use zki_sieve_v3::producers::builder::{BuildGate, GateBuilder, GateBuilderT};
use zki_sieve_v3::structs::types::Type;
use BuildGate::*;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::ptr::NonNull;
use std::rc::Rc;
use zki_sieve_v3::producers::build_gates::NO_OUTPUT;

struct IRWireInner {
    wire: WireId,
    ref_count: usize,
}

pub type Deleted = Rc<RefCell<VecDeque<WireId>>>;

pub struct IRWire {
    inner: NonNull<IRWireInner>,
    freed: Deleted,
}

impl IRWire {
    pub fn new(wire: WireId, freed: Deleted) -> IRWire {
        unsafe {
            let ptr = Box::into_raw(Box::new(IRWireInner {
                wire,
                ref_count: 1,
            }));
            IRWire {
                inner: NonNull::new_unchecked(ptr),
                freed,
            }
        }
    }

    pub fn wire(&self) -> WireId {
        unsafe { (*self.inner.as_ptr()).wire }
    }
}

impl Drop for IRWire {
    /// Destructor for IRWire. Once there is no more reference to this wire, it's automatically
    /// appended to the list of wires to be freed, and the corresponding 'Delete' gate will be
    /// appended to the IR circuit at some point.
    fn drop(&mut self) {
        unsafe {
            let inner = self.inner.as_ptr();
            (*inner).ref_count -= 1;
            if (*inner).ref_count == 0 {
                if (*inner).wire != NO_OUTPUT {
                    self.freed.borrow_mut().push_back((*inner).wire);
                }
                drop(Box::from_raw(inner));
            }
        };
    }
}

impl Clone for IRWire {
    fn clone(&self) -> IRWire {
        let freed = self.freed.clone();
        unsafe {
            // The interior of this block contains no panics.
            (*self.inner.as_ptr()).ref_count += 1;
            IRWire {
                inner: self.inner,
                freed,
            }
        }
    }
}

impl PartialEq<IRWire> for IRWire {
    fn eq(&self, other: &IRWire) -> bool {
        self.wire() == other.wire()
    }
}

impl Eq for IRWire {}

/// Trait for building gates and `IRWire`s.
///
/// The IR builder may be working in a larger underlying field than the `Scalar` field provided by
/// the caller.  As a result, the caller should generally avoid relying on overflow behavior, as
/// the exact values resulting from overflow may vary depending on the field modulus in use.
pub trait IRBuilderT {
    fn zero(&self) -> IRWire;
    fn one(&self) -> IRWire;

    /// The constant value -1 in the underlying field.  This may not match `Scalar::one().neg()`,
    /// depending on the choice of field modulus.
    fn neg_one(&self) -> Value;

    fn create_gate(&mut self, gate: BuildGate) -> IRWire;

    /// Delete `IRWire`s that are no longer used.
    fn free_unused(&mut self);

    fn new_constant(&mut self, value: Value) -> IRWire {
        self.create_gate(Constant(0, value))
    }

    fn new_witness(&mut self, value: Option<Value>) -> IRWire {
        self.create_gate(Private(0, value))
    }

    fn assert_zero(&mut self, wire: &IRWire) {
        self.create_gate(AssertZero(0, wire.wire()));
    }

    /// Compute `left + right`.  Overflow behavior depends on the underyling field, which may not
    /// match the caller's choice of `Scalar` type.
    fn add(&mut self, left: &IRWire, right: &IRWire) -> IRWire {
        self.create_gate(Add(0, left.wire(), right.wire()))
    }

    /// Compute `left + value`.  Overflow behavior depends on the underyling field, which may not
    /// match the caller's choice of `Scalar` type.
    fn addc(&mut self, left: &IRWire, value: Value) -> IRWire {
        self.create_gate(AddConstant(0, left.wire(), value))
    }

    /// Compute `left - right`.  Overflow behavior depends on the underyling field, which may not
    /// match the caller's choice of `Scalar` type.
    fn sub(&mut self, left: &IRWire, right: &IRWire) -> IRWire {
        let neg_right = self.create_gate(MulConstant(0, right.wire(), self.neg_one()));
        self.create_gate(Add(0, left.wire(), neg_right.wire()))
    }

    /// Compute `left - 1`.  Overflow behavior depends on the underyling field, which may not match
    /// the caller's choice of `Scalar` type.
    fn sub1(&mut self, left: &IRWire) -> IRWire {
        self.addc(left, self.neg_one())
    }

    /// Compute `left * right`.  Overflow behavior depends on the underyling field, which may not
    /// match the caller's choice of `Scalar` type.
    fn mul(&mut self, left: &IRWire, right: &IRWire) -> IRWire {
        self.create_gate(Mul(0, left.wire(), right.wire()))
    }

    /// Compute `left * value`.  Overflow behavior depends on the underyling field, which may not
    /// match the caller's choice of `Scalar` type.
    fn mulc(&mut self, left: &IRWire, value: Value) -> IRWire {
        self.create_gate(MulConstant(0, left.wire(), value))
    }

    /// Check that either `num == 0` and `is_zero == 1`, or `num != 0` and `is_zero == 0`.  In
    /// prover mode, `value` must be the value of `num` as a `Scalar`.
    fn check_is_zero<Scalar: PrimeField>(
        &mut self,
        num: &IRWire,
        value: &Option<Scalar>,
        is_zero: &IRWire,
    );

    fn power_of_two(&mut self, n: usize) -> Value;

    /// Give a name to the current context for diagnostics. Multiple calls create a hierarchy of annotations.
    fn annotate(&mut self, _note: &str) {}

    /// Exit the last context that was started with annotate().
    fn deannotate(&mut self) {}
}

/// Extensions to the basic builder.
pub struct IRBuilder<S: Sink> {
    gate_builder: Rc<RefCell<GateBuilder<S>>>,

    /// If dedup is enabled, gates will be deduplicated. Default: enabled.
    /// This affects the resulting relation.
    pub dedup: Option<IRDedup>,

    /// If profiler is enabled, it will track duplicate gates. Default: disabled.
    pub prof: Option<IRProfiler>,

    freed: Deleted,

    zero: Option<IRWire>,
    one: Option<IRWire>,
    neg_one: Value,
    powers_of_two: Vec<Value>,

    extended_modulus: Option<BigUint>,
}

impl<S: 'static + Sink> IRBuilderT for IRBuilder<S> {
    fn zero(&self) -> IRWire {
        self.zero.as_ref().unwrap().clone()
    }

    fn one(&self) -> IRWire {
        self.one.as_ref().unwrap().clone()
    }

    fn neg_one(&self) -> Value {
        self.neg_one.clone()
    }

    fn create_gate(&mut self, gate: BuildGate) -> IRWire {

        if let Some(prof) = &mut self.prof {
            prof.notify_gate(&gate);
        }

        if let Some(dedup) = &mut self.dedup {
            dedup.create_gate(&mut *self.gate_builder.borrow_mut(), gate, self.freed.clone())
        } else {
            IRWire:: new (
                self.gate_builder.borrow_mut().create_gate(gate).unwrap(),
                self.freed.clone()
            )
        }
    }

    fn free_unused(&mut self) {
        if self.freed.borrow().len() >= 10 * 1000 {
            Self::free_unused_inner(&self.freed, &mut self.gate_builder.borrow_mut());
        }
    }

    /// Check that either `num == 0` and `is_zero == 1`, or `num != 0` and `is_zero == 0`.  In
    /// prover mode, `value` must be the value of `num` as a `Scalar`.
    fn check_is_zero<Scalar: PrimeField>(
        &mut self,
        num: &IRWire,
        value: &Option<Scalar>,
        is_zero: &IRWire,
    ) {
        // Enforce that (is_zero * num == 0), then we have:
        //     (num != 0) implies (is_zero == 0)
        // (is_zero != 0) implies (num == 0)
        let product = self.mul(is_zero, num);
        self.assert_zero(&product);

        // Compute the inverse of num.
        // We don't prove that it is necessarily the inverse, but we need it to
        // satisfy the constraint below in the case where (is_zero == 0).
        let inverse_value = value.as_ref().map(|v| {
            match self.extended_modulus {
                None => encode_scalar(&v.invert().unwrap_or_else(|| Scalar::zero())),
                Some(ref m) => {
                    let v = BigUint::from_bytes_le(&encode_scalar(v));
                    mod_inv(&v, m).to_bytes_le()
                },
            }
        });
        let inverse = self.new_witness(inverse_value);

        // Enforce that (num * inverse + is_zero - 1 == 0), then we have:
        //     (num == 0) implies (is_zero == 1)
        // (is_zero != 1) implies (num != 0)
        let num_inverse = self.mul(num, &inverse);
        let n_i_iz = self.add(&num_inverse, is_zero);
        let n_i_iz_1 = self.sub1(&n_i_iz);
        self.assert_zero(&n_i_iz_1);
    }

    /// Return a wire representing constant 2^n.
    /// Cache the constant gates from 0 to n.
    fn power_of_two(&mut self, n: usize) -> Value {
        while self.powers_of_two.len() <= n {
            let exponent = self.powers_of_two.len() as u32;
            let value = BigUint::from(2 as u32).pow(exponent);
            self.powers_of_two.push(value.to_bytes_le());
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
    pub fn new<Scalar: PrimeField>(sink: S, opt_modulus: Option<BigUint>) -> Self {
        let scalar_modulus = get_field_order::<Scalar>();
        let modulus = match opt_modulus.clone() {
            Some(m) => {
                assert!(m >= scalar_modulus,
                    "modulus {} is too small; the minimum allowed is {}", m, scalar_modulus);
                m
            },
            None => scalar_modulus,
        };

        let mut irb = IRBuilder {
            gate_builder: Rc::new(RefCell::new(GateBuilder::new(
                sink,
                &[],
                &[Type::Field(modulus.to_bytes_le())],
                &[],
            ))),
            dedup: Some(IRDedup::default()),
            prof: None, // Some(IRProfiler::default()),
            freed: Deleted::default(),
            zero: None,
            one: None,
            neg_one: vec![],
            powers_of_two: vec![],
            extended_modulus: opt_modulus,
        };

        irb.zero = Some(irb.create_gate(Constant(0, vec![0])));
        // assert_eq!(irb.zero, irb.zero());
        irb.one = Some(irb.create_gate(Constant(0, vec![1])));
        // assert_eq!(irb.one, irb.one());
        irb.neg_one = (modulus - 1_u8).to_bytes_le();
        // assert_eq!(irb.neg_one, irb.neg_one());
        irb.powers_of_two.push(vec![1]);

        irb
    }

    fn free_unused_inner(freed: &Deleted, gate_builder: &mut GateBuilder<S>) {
        let mut freed = freed.borrow_mut();
        if freed.len() == 0 {
            return;
        }

        let mut wires = Vec::with_capacity(freed.len());
        let (a, b) = freed.as_slices();
        wires.extend(a);
        wires.extend(b);
        wires.sort();

        let mut start = wires[0];
        let mut end = wires[0];
        for wire in wires.into_iter().skip(1) {
            if wire == end + 1 {
                end = wire;
            } else {
                if start == end {
                    gate_builder.create_gate(Delete(0, start, start)).unwrap();
                } else {
                    gate_builder.create_gate(Delete(0, start, end)).unwrap();
                }
                start = wire;
                end = wire;
            }
        }

        if start == end {
            gate_builder.create_gate(Delete(0, start, start)).unwrap();
        } else {
            gate_builder.create_gate(Delete(0, start, end)).unwrap();
        }

        freed.clear();
    }

    pub fn finish(self) -> S {
        if let Some(dedup) = self.dedup {
            // clean-up the potential IRWire kept in the memory of the deduplicator.
            drop(dedup);
        }
        drop(self.zero);
        drop(self.one);
        drop(self.powers_of_two);
        Self::free_unused_inner(&self.freed, &mut self.gate_builder.borrow_mut());

        // We can use Rc::try_unwrap() here since we ensures that self.gate_builder is never cloned,
        // so no other Rc<GateBuilder> will exist. And this will never enter the panic!()
        let b = Rc::try_unwrap(self.gate_builder)
            .unwrap_or_else(|_| panic!("Another reference to the GateBuilder exists elsewhere, while it should not!"))
            .into_inner();
        b.finish()
    }

    pub fn disable_dedup(&mut self) {
        self.dedup = None;
    }

    pub fn enable_profiler(&mut self) {
        self.prof = Some(IRProfiler::default());
    }
}


// Based on the code from https://stackoverflow.com/q/68338719
fn mod_inv(n: &BigUint, p: &BigUint) -> BigUint {
    if p.is_one() {
        return BigUint::one();
    }

    let mut a = BigInt::from(n.clone());
    let mut m = BigInt::from(p.clone());
    let mut x = BigInt::zero();
    let mut inv = BigInt::one();

    while a > BigInt::one() {
        let (div, rem) = a.div_rem(&m);
        inv -= div * &x;
        a = rem;
        std::mem::swap(&mut a, &mut m);
        std::mem::swap(&mut x, &mut inv);
    }

    if inv < BigInt::zero() {
        inv += BigInt::from(p.clone());
    }

    inv.try_into().unwrap()
}
