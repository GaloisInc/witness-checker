use scuttlebutt::ring::FiniteRing;
use scuttlebutt::field::F128p;
use crate::ir::circuit::{CircuitTrait, CircuitExt, CircuitBase, CircuitRef, CircuitFilter, AsBits, GateKind, TyKind, Wire, UnOp::Neg, BinOp::{Add, Sub, Mul, Div, Mod}, Field};
use crate::ir::migrate::{self, Migrate};

trait AsField {
    const AS_FIELD: Field;
}

impl AsField for F128p {
    const AS_FIELD: Field = Field::F128p;
}

fn int_field_arith<'a, F: FiniteRing + AsField + AsBits>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    let ty = gk.ty(c);
    let field_ty = c.ty(TyKind::GF(F::AS_FIELD));
    match (gk, *ty) {
        (GateKind::Unary(Neg, a), TyKind::Int(sz) | TyKind::Uint(sz)) => {
            let a_f = c.cast(a, field_ty);
            let two_f = F::ONE + F::ONE;
            let max_f = c.lit(field_ty, two_f.pow(sz.bits() as u128));
            let neg_a_f = c.sub(max_f, a_f);
            c.cast(neg_a_f, ty)
        },
        (GateKind::Binary(Add, a, b), TyKind::Int(_sz) | TyKind::Uint(_sz)) => {
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let sum_f = c.add(a_f, b_f);
            c.cast(sum_f, ty)            
        },
        (GateKind::Binary(Sub, a, b), TyKind::Int(_sz) | TyKind::Uint(_sz)) => {
            // This is necessary to prevent underflowing the field, which
            // is handled by the negation gate.
            c.add(a, c.neg(b))
        },
        (GateKind::Binary(Mul, a, b), TyKind::Int(_sz) | TyKind::Uint(_sz)) => {
            // TODO(isweet): Should we be checking `_sz` to ensure that the
            // designated field is large enough to hold the multiplication?
            // Perhaps callers should be responsible for that?
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let prod_f = c.mul(a_f, b_f);
            c.cast(prod_f, ty)            
        },
        (GateKind::Binary(Div, a, b), TyKind::Int(_sz) | TyKind::Uint(_sz)) => {
            todo!()
        },
        (GateKind::Binary(Mod, a, b), TyKind::Int(_sz) | TyKind::Uint(_sz)) => {
            todo!()
        }
        _ => c.gate(gk),
    }
}

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
