use crate::ir::circuit::{Circuit, CircuitTrait, Wire, TyKind, GateKind, UnOp, CmpOp};

/// Replace `UnOp::Not` with `BinOp::Xor`.
pub fn not_to_xor<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Unary(UnOp::Not, a) = gk {
        if *a.ty == TyKind::BOOL {
            let one = c.lit(a.ty, 1);
            return c.xor(a, one);
        }
    }
    c.gate(gk)
}

/// Replace comparison operations on booleans with standard logical operations.
pub fn compare_to_logic<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Compare(op, a, b) = gk {
        if *a.ty == TyKind::BOOL {
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
    c.gate(gk)
}

/// Lower mux on booleans to ands and ors.
pub fn mux<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Mux(cond, t, e) = gk {
        if *t.ty == TyKind::BOOL {
            return c.or(c.and(cond, t), c.and(c.not(cond), e));
        }
    }
    c.gate(gk)
}



pub struct Adapter<C>(pub C);

impl<'a, C: CircuitTrait<'a>> CircuitTrait<'a> for Adapter<C> {
    type Inner = C;
    fn inner(&self) -> &C { &self.0 }

    fn gate(&self, gk: GateKind<'a>) -> Wire<'a> {
        if *gk.ty(self) != TyKind::BOOL {
            return self.inner().gate(gk);
        }

        let c = self;
        if let GateKind::Mux(cond, t, e) = gk {
            c.or(c.and(cond, t), c.and(c.not(cond), e))
        } else if let GateKind::Compare(op, a, b) = gk {
            if *a.ty != TyKind::BOOL {
                return self.inner().gate(gk);
            }
            match op {
                CmpOp::Eq => c.not(c.xor(a, b)),
                CmpOp::Ne => c.xor(a, b),
                CmpOp::Lt => c.and(c.not(a), b),
                CmpOp::Le => c.or(c.not(a), b),
                CmpOp::Gt => c.and(c.not(b), a),
                CmpOp::Ge => c.or(c.not(b), a),
            }
        } else if let GateKind::Unary(UnOp::Not, a) = gk {
            let one = c.lit(a.ty, 1);
            c.xor(a, one)
        } else {
            self.inner().gate(gk)
        }
    }
}
