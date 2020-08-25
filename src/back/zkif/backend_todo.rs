use crate::ir::circuit::{Circuit, Wire, GateKind, TyKind, UnOp, CmpOp, BinOp};

pub fn ignore_gates_todo<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    match gk {
        GateKind::Unary(UnOp::Not, arg) => match *arg.ty {
            TyKind::Int(_) | TyKind::Uint(_) =>
                return arg,
            _ => {}
        }

        GateKind::Binary(op, arg, _) => match *arg.ty {
            TyKind::Bool => match op {
                BinOp::Div | BinOp::Mod =>
                    return arg,
                _ => {}
            }

            TyKind::Int(_) | TyKind::Uint(_) => match op {
                BinOp::Div | BinOp::Mod | BinOp::And | BinOp::Or | BinOp::Xor =>
                    return arg,
                _ => {}
            }

            _ => {}
        }

        GateKind::Shift(_, arg, _) =>
            return arg,

        GateKind::Compare(CmpOp::Lt, _, _) =>
            return c.lit(c.ty(TyKind::Bool), 1),

        _ => {}
    }

    c.gate(gk)
}
