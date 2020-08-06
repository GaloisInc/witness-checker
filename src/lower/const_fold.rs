use crate::ir::circuit::{Circuit, Ty, Wire, GateKind, TyKind, UnOp, BinOp, ShiftOp, CmpOp};

fn get_const<'a>(w: Wire<'a>) -> Option<u64> {
    match w.kind {
        GateKind::Lit(val, _) => Some(val),
        _ => None,
    }
}

fn value_mask(ty: Ty) -> Option<u64> {
    match *ty {
        TyKind::Bool => Some(1),
        TyKind::Int(sz) |
        TyKind::Uint(sz) => Some(!0 >> (64 - sz.bits())),
        TyKind::Bundle(_) => None,
    }
}

fn sign_extend(ty: Ty, val: u64) -> Option<i64> {
    let shift = match *ty {
        TyKind::Int(sz) | TyKind::Uint(sz) => 64 - sz.bits(),
        _ => return None,
    };
    Some(((val << shift) as i64) >> shift)
}

fn try_const_fold<'a>(c: &Circuit<'a>, gk: GateKind<'a>) -> Option<u64> {
    match gk {
        // `Lit` is already a constant - no need for more folding.
        GateKind::Lit(..) => None,
        GateKind::Secret(..) => None,
        GateKind::Unary(op, a) => {
            let a_val = get_const(a)?;
            let ty = a.ty;
            let val = match op {
                UnOp::Not => !a_val,
                UnOp::Neg => sign_extend(ty, a_val)?.wrapping_neg() as u64,
            };
            Some(val & value_mask(ty)?)
        },
        GateKind::Binary(op, a, b) => {
            let a_val = get_const(a)?;
            let b_val = get_const(b)?;
            let ty = a.ty;
            let val = match (op, *ty) {
                (BinOp::Add, _) => a_val.wrapping_add(b_val),
                (BinOp::Sub, _) => a_val.wrapping_sub(b_val),
                (BinOp::Mul, _) => a_val.wrapping_mul(b_val),
                (BinOp::Div, TyKind::Uint(_)) => a_val / b_val,
                (BinOp::Div, TyKind::Int(_)) =>
                    (sign_extend(ty, a_val)? / sign_extend(ty, b_val)?) as u64,
                (BinOp::Div, _) => return None,
                (BinOp::Mod, TyKind::Uint(_)) => a_val % b_val,
                (BinOp::Mod, TyKind::Int(_)) =>
                    (sign_extend(ty, a_val)? % sign_extend(ty, b_val)?) as u64,
                (BinOp::Mod, _) => return None,
                (BinOp::And, _) => a_val & b_val,
                (BinOp::Or, _) => a_val | b_val,
                (BinOp::Xor, _) => a_val ^ b_val,
            };
            Some(val & value_mask(ty)?)
        },
        GateKind::Shift(op, a, b) => {
            let a_val = get_const(a)?;
            let b_val = get_const(b)?;
            let ty = a.ty;
            let val = match (op, *ty) {
                (ShiftOp::Shl, _) => a_val << b_val,
                (ShiftOp::Shr, TyKind::Uint(_)) => a_val >> b_val,
                (ShiftOp::Shr, TyKind::Int(_)) =>
                    (sign_extend(ty, a_val)? >> b_val) as u64,
                (ShiftOp::Shr, _) => return None,
            };
            Some(val & value_mask(ty)?)
        },
        GateKind::Compare(op, a, b) => {
            let a_val = get_const(a)?;
            let b_val = get_const(b)?;
            let ty = a.ty;
            let val: bool = match (op, *ty) {
                (CmpOp::Eq, _) => (a_val & value_mask(ty)?) == (b_val & value_mask(ty)?),
                (CmpOp::Ne, _) => (a_val & value_mask(ty)?) != (b_val & value_mask(ty)?),
                (CmpOp::Lt, TyKind::Int(_)) => sign_extend(ty, a_val)? < sign_extend(ty, b_val)?,
                (CmpOp::Lt, _) => a_val < b_val,
                (CmpOp::Le, TyKind::Int(_)) => sign_extend(ty, a_val)? <= sign_extend(ty, b_val)?,
                (CmpOp::Le, _) => a_val <= b_val,
                (CmpOp::Gt, TyKind::Int(_)) => sign_extend(ty, a_val)? > sign_extend(ty, b_val)?,
                (CmpOp::Gt, _) => a_val > b_val,
                (CmpOp::Ge, TyKind::Int(_)) => sign_extend(ty, a_val)? >= sign_extend(ty, b_val)?,
                (CmpOp::Ge, _) => a_val >= b_val,
            };
            Some(val as u64)
        },
        GateKind::Mux(c, t, e) => {
            let c_val = get_const(c)?;
            let t_val = get_const(t)?;
            let e_val = get_const(e)?;
            let val = if c_val != 0 { t_val } else { e_val };
            Some(val)
        },
        GateKind::Cast(a, new_ty) => {
            let a_val = get_const(a)?;
            let val = match *a.ty {
                TyKind::Int(_) => sign_extend(a.ty, a_val)? as u64,
                _ => a_val,
            };
            Some(val & value_mask(new_ty)?)
        },
        GateKind::Pack(_) => None,
        GateKind::Extract(w, i) => {
            match w.kind {
                GateKind::Pack(ws) => get_const(ws[i]),
                _ => None,
            }
        },
        GateKind::Gadget(k, ws) => {
            if !ws.iter().all(|&w| get_const(w).is_some()) {
                return None;
            }
            // All inputs are constants.  This should mean that the gadget itself can be
            // const-evaluated.
            let w = k.decompose(c, ws);
            // Recursively calling `run_pass` is normally a bad idea because the recursive call
            // usse a fresh memo table, sharing nothing with the original `RunPass` instance, so in
            // can lead to exponential runtime.  In this case, we expect it to be okay because we
            // already know every input in `ws` is a `Lit`, which contains no wires and thus no
            // sharing.  However, this could break if the `GadgetKind` itself contains a `Wire`
            // (which would normally be a bad idea, since `run_pass` couldn't see that wire).
            let new_w = super::run_pass(c, vec![w], const_fold)[0];
            get_const(new_w)
        },
    }
}

/// Like `try_const_fold`, but applies specific rules for certain cases where only some inputs are
/// known.
fn try_identities<'a>(c: &Circuit<'a>, gk: GateKind<'a>) -> Option<Wire<'a>> {
    let ty = gk.ty(c);
    Some(match gk {
        GateKind::Binary(op, a, b) => match (op, get_const(a), get_const(b)) {
            // x + 0 = 0 + x = x
            (BinOp::Add, Some(0), None) => b,
            (BinOp::Add, None, Some(0)) => a,
            // x - 0 = x
            (BinOp::Sub, None, Some(0)) => a,
            // x - x = 0
            (BinOp::Sub, None, None) if a == b => c.lit(ty, 0),
            // 0 * x = x * 0 = 0
            (BinOp::Mul, Some(0), None) => c.lit(ty, 0),
            (BinOp::Mul, None, Some(0)) => c.lit(ty, 0),
            // 0 / x = 0
            (BinOp::Div, Some(0), None) => c.lit(ty, 0),
            // x / x = 1
            (BinOp::Div, None, None) if a == b => c.lit(ty, 1),
            // 0 % x = 0
            (BinOp::Mod, Some(0), None) => c.lit(ty, 0),
            // x % x = 0
            (BinOp::Mod, None, None) if a == b => c.lit(ty, 0),

            // 0 & x = x & 0 = 0
            (BinOp::And, Some(0), None) => c.lit(ty, 0),
            (BinOp::And, None, Some(0)) => c.lit(ty, 0),
            // !0 & x = x & !0 = x
            (BinOp::And, Some(m), None) if Some(m) == value_mask(ty) => b,
            (BinOp::And, None, Some(m)) if Some(m) == value_mask(ty) => a,
            // x & x = x
            (BinOp::And, None, None) if a == b => a,

            // 0 | x = x | 0 = x
            (BinOp::Or, Some(0), None) => b,
            (BinOp::Or, None, Some(0)) => a,
            // !0 | x = x | !0 = !0
            (BinOp::Or, Some(m), None) if Some(m) == value_mask(ty) =>
                c.lit(ty, value_mask(ty)?),
            (BinOp::Or, None, Some(m)) if Some(m) == value_mask(ty) =>
                c.lit(ty, value_mask(ty)?),
            // x | x = x
            (BinOp::Or, None, None) if a == b => a,

            // 0 ^ x = x ^ 0 = x
            (BinOp::Xor, Some(0), None) => b,
            (BinOp::Xor, None, Some(0)) => a,
            // !0 ^ x = x ^ !0 = !x
            (BinOp::Xor, Some(m), None) if Some(m) == value_mask(ty) => c.not(b),
            (BinOp::Xor, None, Some(m)) if Some(m) == value_mask(ty) => c.not(a),
            // x ^ x = 0
            (BinOp::Xor, None, None) if a == b => c.lit(ty, 0),

            _ => return None,
        },
        GateKind::Shift(op, a, b) => match (op, get_const(a), get_const(b)) {
            // x << 0 = x >> 0 = x
            (ShiftOp::Shl, None, Some(0)) => a,
            (ShiftOp::Shr, None, Some(0)) => a,
            _ => return None,
        },
        GateKind::Compare(op, a, b) => match (op, *ty, get_const(a), get_const(b)) {
            // x == x, x <= x, x >= x: true
            (CmpOp::Eq, _, None, None) if a == b => c.lit(c.ty(TyKind::Bool), 1),
            (CmpOp::Le, _, None, None) if a == b => c.lit(c.ty(TyKind::Bool), 1),
            (CmpOp::Ge, _, None, None) if a == b => c.lit(c.ty(TyKind::Bool), 1),
            // x != x, x < x, x > x: false
            (CmpOp::Ne, _, None, None) if a == b => c.lit(c.ty(TyKind::Bool), 0),
            (CmpOp::Gt, _, None, None) if a == b => c.lit(c.ty(TyKind::Bool), 0),
            (CmpOp::Lt, _, None, None) if a == b => c.lit(c.ty(TyKind::Bool), 0),

            // (unsigned) x >= 0, 0 <= x: true
            (CmpOp::Ge, TyKind::Uint(_), None, Some(0)) => c.lit(c.ty(TyKind::Bool), 1),
            (CmpOp::Le, TyKind::Uint(_), Some(0), None) => c.lit(c.ty(TyKind::Bool), 1),
            // (unsigned) x < 0, 0 > x: false
            (CmpOp::Gt, TyKind::Uint(_), None, Some(0)) => c.lit(c.ty(TyKind::Bool), 0),
            (CmpOp::Lt, TyKind::Uint(_), Some(0), None) => c.lit(c.ty(TyKind::Bool), 0),

            _ => return None,
        },
        GateKind::Mux(c, t, e) => match get_const(c) {
            Some(0) => e,
            Some(1) => t,
            None if t == e => t,
            _ => return None,
        },
        _ => return None,
    })
}

pub fn const_fold<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    match try_const_fold(c, gk) {
        Some(val) => return c.lit(gk.ty(c), val),
        None => {},
    }
    match try_identities(c, gk) {
        Some(w) => return w,
        None => {},
    }
    c.gate(gk)
}

