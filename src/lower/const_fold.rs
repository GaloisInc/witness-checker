use crate::eval::{self, CachingEvaluator};
use crate::ir::circuit::{Circuit, Ty, Wire, GateKind, TyKind, BinOp, ShiftOp, CmpOp};

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

pub fn const_fold<'a, 'c>(
    c: &'c Circuit<'a>,
) -> impl FnMut(&Circuit<'a>, Wire, GateKind<'a>) -> Wire<'a> + 'c {
    let mut e = CachingEvaluator::<eval::Public>::new(c);
    move |c, _old, gk| {
        match eval::eval_gate(&mut e, gk) {
            Some(eval::Value::Single(val)) => return c.lit(gk.ty(c), val),
            _ => {},
        }
        match try_identities(c, gk) {
            Some(w) => return w,
            None => {},
        }
        c.gate(gk)
    }
}

