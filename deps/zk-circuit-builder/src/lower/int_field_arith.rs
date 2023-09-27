use scuttlebutt::ring::FiniteRing;
use scuttlebutt::field::F128p;
use crate::ir::circuit::{CircuitTrait, CircuitExt, CircuitRef, CircuitFilter, GateKind, TyKind, Wire, UnOp::Neg, BinOp::{Add, Sub, Mul, Div, Mod}, Field};

pub fn int_field_arith<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    let ty = gk.ty(c);
    let field_ty = c.ty(TyKind::GF(Field::F128p));
    match (gk, *ty) {
        (GateKind::Unary(Neg, a), TyKind::Int(sz) | TyKind::Uint(sz)) => {
            let a_f = c.cast(a, field_ty);
            let two_f = F128p::ONE + F128p::ONE;
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
