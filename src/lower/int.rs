use crate::ir::circuit::{Circuit, Wire, GateKind, CmpOp};

// TODO: mod -> div + sub

pub fn compare_to_zero<'a>(c: &Circuit<'a>, _old: GateKind, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Compare(op, a, b) = gk {
        if a.ty.kind.is_integer() {
            let zero = c.lit(a.ty, 0);
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
    c.gate(gk)
}

pub fn mux<'a>(c: &Circuit<'a>, _old: GateKind, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Mux(cond, t, e) = gk {
        if t.ty.kind.is_integer() {
            let mask = c.neg(c.cast(cond, t.ty));
            return c.or(c.and(mask, t), c.and(c.not(mask), e));
        }
    }
    c.gate(gk)
}
