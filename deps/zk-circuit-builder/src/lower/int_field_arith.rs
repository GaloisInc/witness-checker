use scuttlebutt::ring::FiniteRing;
use scuttlebutt::field::F128p;
use crate::ir::circuit::{CircuitTrait, CircuitExt, CircuitBase, CircuitRef, CircuitFilter, AsBits, FromBits, GateKind, TyKind, Wire, Bits, UnOp::Neg, BinOp::{Add, Sub, Mul, Div, Mod}, Field, IntSize};
use crate::ir::migrate::{self, Migrate};

trait AsField {
    const AS_FIELD: Field;
}

impl AsField for F128p {
    const AS_FIELD: Field = Field::F128p;
}

fn int_field_arith<'a, F: FiniteRing + AsField + FromBits + AsBits>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    let ty = gk.ty(c);
    let field_ty = c.ty(TyKind::GF(F::AS_FIELD));
    match gk {
        GateKind::Unary(Neg, a) if ty.is_integer() => {
            let a_f = c.cast(a, field_ty);
            let two_f = F::ONE + F::ONE;
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
        GateKind::Binary(op @ Div, a, b) | GateKind::Binary(op @ Mod, a, b) if ty.is_int() => {
            let a_f = c.cast(a, field_ty);
            let quot_f = c.secret_derived(field_ty, c.wire_list(&[a, b]), move |c, vs| {
                match vs {
                    [a_bits, b_bits] => {
                        let a = a_bits.to_biguint();
                        let b = b_bits.to_biguint();
                        let quot = a / b;
                        // TODO(isweet): Convert to a field element
                        todo!()
                    }
                    _ => unreachable!(),
                }
            });
            let b_f = c.cast(b, field_ty);
            let rem_f = todo!();
            let quot_times_denom_f = c.mul(quot_f, b_f);
            let num_minus_rem_f = c.sub(a_f, rem_f);
            let diff_all = c.sub(quot_times_denom_f, num_minus_rem_f);
            c.seq(c.assert_zero(diff_all), {
                let width = (*b.ty).integer_size().bits();
                let neg_check_ty = c.ty(TyKind::Int(IntSize(width + 1)));
                let rem_minus_denom = c.cast(c.sub(rem_f, b_f), neg_check_ty);
                let rem_minus_denom_is_neg = c.lt(rem_minus_denom, c.lit(neg_check_ty, 0));
                let denom_zero = c.eq(b, c.lit(b.ty, 0));
                let ok = c.or(rem_minus_denom_is_neg, denom_zero);
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

// TODO(isweet): Consider making the field a phantom type instead
// TODO(isweet): Add `HashMap<Wire<'a>, ...>` to implement lazy truncation.
//   Q: What order are passes executed in? Does this pass need to be last to work
//      correctly? My concern is that I'll map some wire `a` to a value, and then `a`
//      will be elaborated in a later pass?
//
//      e.g. `Binary(Add, Binary(Add, Lit(1, U64), Lit(2, U64)), Secret)` where `a,b : Uint(64)`
//           This pass will map: `Lit(3, U64) => 2`, `Lit(5, U64) => 3`
//           Then, const fold will do nothing.
//           Then, this pass will map: `Binary(Add, Lit(1, U64), Lit(2, U64)) => max(2, 3) + 1 == 4`
//           But then, the const fold pass will elaborate that gate and create `Binary(Add, Lit(3, U64), Secret)`
//           Then, when this pass runs again it will lookup `Lit(3, U64)` in the map and not find it? Or will
//           this pass run on the newly created `Lit(3, U64)` that was created by the constant folding pass?
//           ... I'm confused :)
//
//   Q: Also, do wires that have been elaborated away (like `Lit(1, U64)` above) get de-allocated? Will my map
//      grow to the size of the entire circuit?
pub struct IntFieldArith<F>(pub F, pub Option<Field>);

impl<'a, F: CircuitFilter<'a> + 'a> CircuitFilter<'a> for IntFieldArith<F>
where F: Migrate<'a, 'a, Output = F> {
    circuit_filter_common_methods!();

    fn gate(&self, base: &CircuitBase<'a>, gk: GateKind<'a>) -> Wire<'a> {
        let c = CircuitRef { base, filter: &self.0 };
        match self.1 {
            None => c.gate(gk),
            Some(Field::F128p) => int_field_arith::<F128p>(&c, gk),
            _ => unimplemented!()
        }
    }
}

impl<'a, 'b, F> Migrate<'a, 'b> for IntFieldArith<F>
where
    F: Migrate<'a, 'b>,
{
    type Output = IntFieldArith<F::Output>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        IntFieldArith(v.visit(self.0), self.1)
    }
}
