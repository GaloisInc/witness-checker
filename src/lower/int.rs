use crate::ir::circuit::{Circuit, Gate, Wire, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};

// TODO: mod -> div + sub

fn compare_to_zero<'a>(c: &Circuit<'a>, g: Gate<'a>) -> Wire<'a> {
    if g.ty.kind.is_integer() {
        if let GateKind::Compare(op, a, b) = g.kind {
            let zero = c.lit(g.ty, 0);
            return match op {
                CmpOp::Eq => c.eq(c.sub(a, b), zero),
                CmpOp::Ne => c.not(c.eq(c.sub(a, b), zero)),
                CmpOp::Lt => c.lt(c.sub(a, b), zero),
                CmpOp::Le => c.not(c.lt(c.sub(b, a), zero)),
                CmpOp::Gt => c.lt(c.sub(b, a), zero),
                CmpOp::Ge => c.not(c.lt(c.sub(a, b), zero)),
            };
        }
    }
    c.gate(g)
}

fn mux<'a>(c: &Circuit<'a>, g: Gate<'a>) -> Wire<'a> {
    if g.ty.kind.is_integer() {
        if let GateKind::Mux(cond, t, e) = g.kind {
            let mask = c.neg(c.cast(cond, g.ty.kind));
            return c.or(c.and(mask, t), c.and(c.not(mask), e));
        }
    }
    c.gate(g)
}
