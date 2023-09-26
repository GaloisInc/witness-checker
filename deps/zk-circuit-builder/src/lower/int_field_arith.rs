use crate::ir::circuit::{CircuitTrait, CircuitExt, CircuitRef, CircuitFilter, GateKind, TyKind, Wire, UnOp::Neg, BinOp::{Add, Sub, Mul}, Field::F128p};

pub fn int_field_arith<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    let ty = gk.ty(c);
    let field_ty = c.ty(TyKind::GF(F128p));
    match (gk, *ty) {
        (GateKind::Unary(Neg, a), TyKind::Int(sz) | TyKind::Uint(sz)) => {
            let a_f = c.cast(a, field_ty);
            let max_f = todo!();
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
            c.add(a, c.neg(b))
        },
        (GateKind::Binary(Mul, a, b), TyKind::Int(_sz) | TyKind::Uint(_sz)) => {
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let prod_f = c.mul(a_f, b_f);
            c.cast(prod_f, ty)            
        }
        _ => c.gate(gk),
    }
}
