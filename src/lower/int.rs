use crate::ir::circuit::{Circuit, Ty, Wire, GateKind, TyKind, IntSize, CmpOp};

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


fn maybe_sign_extend(x: u64, ty: Ty) -> u64 {
    match ty.kind {
        TyKind::Uint(_sz) => x,
        TyKind::Int(sz) => {
            let y = x as i64;
            // Sign-extend to 64 bits
            let y = y << (64 - sz.bits()) >> (64 - sz.bits());
            y as u64
        },
        _ => panic!("expected Uint or Int, but got {:?}", ty.kind),
    }
}

fn extend_integer_ty(ty: Ty) -> Ty {
    match ty.kind {
        TyKind::Uint(_) => Ty::new(TyKind::U64),
        TyKind::Int(_) => Ty::new(TyKind::I64),
        _ => panic!("expected Uint or Int, but got {:?}", ty.kind),
    }
}

/// Normalize `w` to a valid 64-bit representation of `ty`.  For example, if `ty` is `U8`, then `w`
/// will be masked to retain only the lower 8 bits.
fn normalize_64<'a>(c: &Circuit<'a>, w: Wire<'a>, ty: Ty) -> Wire<'a> {
    let bits = ty.kind.integer_size().bits();
    if bits >= 64 {
        return w;
    }
    match ty.kind {
        TyKind::Uint(_) => {
            let mask = !(!0_u64 << bits);
            c.and(w, c.lit(Ty::new(TyKind::U64), mask))
        },
        TyKind::Int(_) => {
            let shift_amount = c.lit(Ty::new(TyKind::U8), 64 - bits as u64);
            c.shr(c.shl(w, shift_amount), shift_amount)
        },
        _ => panic!("expected Uint or Int, but got {:?}", ty.kind),
    }

}

/// Extend all integers to 64 bits.  That is, all `Uint`s will be extended to `U64`, and all `Int`s
/// will be extended to `I64`.
pub fn extend_to_64<'a>(c: &Circuit<'a>, old: GateKind, gk: GateKind<'a>) -> Wire<'a> {
    if old.ty().kind.is_integer() && old.ty().kind.integer_size() != IntSize::I64 {
        match gk {
            GateKind::Lit(x, ty) => {
                return c.lit(extend_integer_ty(ty), maybe_sign_extend(x, ty));
            },
            GateKind::Secret(s) => {
                let new_ty = extend_integer_ty(s.ty);
                let new_val = s.val.map(|x| maybe_sign_extend(x, s.ty));
                return c.new_secret(new_ty, new_val);
            },
            GateKind::Cast(w, ty) => {
                return normalize_64(c, w, ty);
            },
            // Currently, we normalize (zero/sign-extending to fill the high bits) after every
            // operation.  We could instead let the high bits be arbitrary and normalize only when
            // needed: at comparisons, shifts, and outputs.  However, we don't currently have a
            // good way to tell if a gate will be used as an output.
            _ => {
                return normalize_64(c, c.gate(gk), old.ty());
            },
        }
    }
    c.gate(gk)
}
