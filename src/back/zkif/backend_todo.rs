use crate::ir::circuit::{Circuit, Wire, GateKind, TyKind, UnOp, CmpOp, BinOp};
use crate::ir::circuit::IntSize::{I64, I32};

pub fn ignore_gates_todo<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    match gk {

        // Downgrade to 32 bits.
        GateKind::Lit(val, ty) => match *ty {
            TyKind::Int(I64) =>
                return c.lit(c.ty(TyKind::Int(I32)), val as i32 as u64),
            TyKind::Uint(I64) =>
                return c.lit(c.ty(TyKind::Uint(I32)), val as u32 as u64),
            _ => {}
        }

        // Downgrade to 32 bits.
        GateKind::Secret(secret) => match *secret.ty {
            TyKind::Int(I64) =>
                return c.new_secret(
                    c.ty(TyKind::Int(I32)),
                    secret.val.map(|val| val as i32 as u64)),
            TyKind::Uint(I64) =>
                return c.new_secret(
                    c.ty(TyKind::Uint(I32)),
                    secret.val.map(|val| val as u32 as u64)),
            _ => {}
        }

        // Downgrade to 32 bits.
        GateKind::Cast(arg, ty) => match *ty {
            TyKind::Int(I64) =>
                return c.cast(arg, c.ty(TyKind::Int(I32))),
            TyKind::Uint(I64) =>
                return c.cast(arg, c.ty(TyKind::Uint(I32))),
            _ => {}
        }

        GateKind::Binary(op, arg, _) => match *arg.ty {
            TyKind::Bool => match op {
                BinOp::Div | BinOp::Mod =>
                    return c.gate(arg.kind),
                _ => {}
            }

            TyKind::Int(_) | TyKind::Uint(_) => match op {
                BinOp::Div =>
                    return c.gate(arg.kind),
                _ => {}
            }

            _ => {}
        }

        GateKind::Compare(CmpOp::Lt, _, _) =>
            return c.lit(c.ty(TyKind::Bool), 1),

        _ => {}
    }

    c.gate(gk)
}
