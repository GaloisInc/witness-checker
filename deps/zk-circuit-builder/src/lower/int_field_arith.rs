use num_bigint::{BigUint, ToBigInt};
use num_traits::Zero;
use scuttlebutt::field::PrimeFiniteField;
use scuttlebutt::field::F128p;
use crate::ir::circuit::{CircuitTrait, CircuitExt, CircuitBase, CircuitRef, CircuitFilter, AsBits, FromBits, GateKind, TyKind, Wire, Bits, UnOp::Neg, BinOp::{Add, Sub, Mul, Div, Mod}, Field, IntSize, Ty};
use crate::eval::bigint_to_prime_field_bits;
use crate::ir::migrate::{self, Migrate};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::collections::HashMap;
use std::convert::TryInto;

trait AsField {
    const AS_FIELD: Field;
}

impl AsField for F128p {
    const AS_FIELD: Field = Field::F128p;
}

fn int_field_arith<'a, F: PrimeFiniteField + AsField + FromBits + AsBits>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a>
where
    F::Error: Debug,
{
    let ty = gk.ty(c);
    let field_ty = c.ty(TyKind::GF(F::AS_FIELD));
    match gk {
        GateKind::Unary(Neg, a) if ty.is_integer() => {
            let a_f = c.cast(a, field_ty);
            let two_f = F::try_from(2 as u128).unwrap();
            let max_f = c.lit(field_ty, two_f.pow(ty.integer_size().bits() as u128));
            let neg_a_f = c.sub(max_f, a_f);
            c.cast(neg_a_f, ty)
        },
        GateKind::Binary(Add, a, b) if ty.is_integer() => {
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let sum_f = c.add(a_f, b_f);
            c.cast(sum_f, ty)            
        },
        GateKind::Binary(Sub, a, b) if ty.is_integer() => {
            // This is necessary to prevent underflowing the field, which
            // is handled by the negation gate.
            c.add(a, c.neg(b))
        },
        GateKind::Binary(Mul, a, b) if ty.is_integer() => {
            // TODO(isweet): Should we be checking `_sz` to ensure that the
            // designated field is large enough to hold the multiplication?
            // Perhaps callers should be responsible for that?
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let prod_f = c.mul(a_f, b_f);
            c.cast(prod_f, ty)            
        },
        GateKind::Binary(op @ Div, a, b) | GateKind::Binary(op @ Mod, a, b) if ty.is_uint() => {
            let width = ty.integer_size();
            let quot_f = c.secret_derived(field_ty, c.wire_list(&[a, b]), move |c, vs| {
                let [a_bits, b_bits]: [Bits; 2] = vs.try_into().unwrap();
                let a = a_bits.to_biguint();
                let b = b_bits.to_biguint();
                let quot = if b.is_zero() { BigUint::zero() } else { a / b };
                bigint_to_prime_field_bits(c, quot.to_bigint().unwrap(), width, F::AS_FIELD)
            });
            let rem_f = c.secret_derived(field_ty, c.wire_list(&[a, b]), move |c, vs| {
                let [a_bits, b_bits]: [Bits; 2] = vs.try_into().unwrap();
                let a = a_bits.to_biguint();
                let b = b_bits.to_biguint();
                let rem = if b.is_zero() { a } else { a % b };
                bigint_to_prime_field_bits(c, rem.to_bigint().unwrap(), width, F::AS_FIELD)
            });
            
            let a_f = c.cast(a, field_ty);            
            let b_f = c.cast(b, field_ty);
            let quot_times_denom_f = c.mul(quot_f, b_f);               // q * b
            let num_minus_rem_f = c.sub(a_f, rem_f);                   // a - r
            let diff_all = c.sub(quot_times_denom_f, num_minus_rem_f); // (q * b) - (a - r)

            let width = (*b.ty).integer_size().bits();
            let neg_check_ty = c.ty(TyKind::Int(IntSize(width + 1)));
            let rem_int = c.cast(rem_f, neg_check_ty);
            let b_int = c.cast(b, neg_check_ty);
            let rem_minus_denom = c.sub(rem_int, b_int);                                // r - b
            let rem_minus_denom_is_neg = c.lt(rem_minus_denom, c.lit(neg_check_ty, 0)); // r - b < 0 (i.e. r < b)
            let denom_zero = c.eq(b, c.lit(b.ty, 0));                                   // b == 0
            let ok = c.or(rem_minus_denom_is_neg, denom_zero);                          // r < b \/ b == 0
            
            // Asserts that q * b - (a - r) == 0 (which implies that a == q * b + r)
            c.seq(c.assert_zero(diff_all), {
                // Asserts that either the remainder is less than the denominator, or the denominator is zero
                c.seq(c.assert_zero(c.not(ok)), c.cast(match op {
                    Div => quot_f,
                    Mod => rem_f,
                    _   => unreachable!(),
                }, ty))
            })
        },
        _ => c.gate(gk),
    }
}

struct NumBounds {
    valid_bits: u16,
    real_bits: u16,
}

pub struct IntFieldArith<'a, F, P> {
    inner: F,
    _field: PhantomData<P>,
    active: bool,
    bounds: HashMap<Wire<'a>, NumBounds>,
}

impl<'a, F, P> IntFieldArith<'a, F, P> {
    pub fn new(inner: F, active: bool) -> Self {
        IntFieldArith {
            inner,
            _field: PhantomData,
            active,
            bounds: HashMap::new(),
        }
    }
}
    
impl<'a, F: CircuitFilter<'a> + 'a, P: PrimeFiniteField + AsField + FromBits + AsBits> CircuitFilter<'a> for IntFieldArith<'a, F, P>
where F: Migrate<'a, 'a, Output = F>,
      P::Error: Debug,
{
    circuit_filter_common_methods!();

    fn gate(&self, base: &CircuitBase<'a>, gk: GateKind<'a>) -> Wire<'a> {
        let c = CircuitRef { base, filter: &self.inner };

        if self.active {
            return int_field_arith::<P>(&c, gk);
        }

        c.gate(gk)
    }
}

impl<'a, 'b, F, P> Migrate<'a, 'b> for IntFieldArith<'a, F, P>
where
    F: Migrate<'a, 'b>,
{
    type Output = IntFieldArith<'b, F::Output, P>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        let mut bounds = HashMap::new();
        for (old_wire, old_repr) in self.bounds {
            let new_wire = match v.visit_wire_weak(old_wire) {
                Some(x) => x,
                None => continue,
            };
            
            bounds.insert(new_wire, old_repr);
        }
        
        IntFieldArith {
            inner: v.visit(self.inner),
            _field: PhantomData,
            active: self.active,
            bounds,
        }
    }
}
