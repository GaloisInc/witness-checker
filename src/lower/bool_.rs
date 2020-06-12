use crate::ir::circuit::{Circuit, Gate, Wire, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};

/// Replace `UnOp::Not` with `BinOp::Xor`.
pub fn not_to_xor<'a>(c: &Circuit<'a>, g: Gate<'a>) -> Wire<'a> {
    if g.ty.kind == TyKind::Bool {
        if let GateKind::Unary(UnOp::Not, a) = g.kind {
            let one = c.lit(g.ty, 1);
            return c.xor(a, one);
        }
    }
    c.gate(g)
}

/// Replace comparison operations on booleans with standard logical operations.
pub fn compare_to_logic<'a>(c: &Circuit<'a>, g: Gate<'a>) -> Wire<'a> {
    // Note the usual pattern of checking `g.ty.kind` fails here, since all comparison gates have
    // `Bool` outputs.
    if let GateKind::Compare(op, a, b) = g.kind {
        if a.ty.kind == TyKind::Bool {
            eprintln!("fired {:?}",g);
            return match op {
                CmpOp::Eq => c.not(c.xor(a, b)),
                CmpOp::Ne => c.xor(a, b),
                CmpOp::Lt => c.and(c.not(a), b),
                CmpOp::Le => c.or(c.not(a), b),
                CmpOp::Gt => c.and(c.not(b), a),
                CmpOp::Ge => c.or(c.not(b), a),
            };
        }
    }
    c.gate(g)
}

/// Lower mux on booleans to ands and ors.
pub fn mux<'a>(c: &Circuit<'a>, g: Gate<'a>) -> Wire<'a> {
    if g.ty.kind == TyKind::Bool {
        if let GateKind::Mux(cond, t, e) = g.kind {
            return c.or(c.and(cond, t), c.and(c.not(cond), e));
        }
    }
    c.gate(g)
}
