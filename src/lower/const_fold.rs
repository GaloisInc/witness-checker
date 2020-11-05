use num_bigint::BigInt;
use num_traits::{Zero, One};
use crate::eval::{self, CachingEvaluator, Evaluator, Value};
use crate::ir::circuit::{Circuit, Ty, Wire, GateKind, TyKind, IntSize, BinOp, ShiftOp, CmpOp};

macro_rules! match_identities {
    (
        $op:expr, ($($arg:expr),*);
        vars $vars:tt;
        eval $eval:expr;
        $(
            $op_pat:pat, $conds:tt $( if $guard:expr )? => $val:expr,
        )*
    ) => {{
        bind_vars!($eval, $vars, ($($arg,)*));
        match $op {
            $(
                $op_pat if apply_conds!($vars, $conds) $( && $guard )? => $val,
            )*
            _ => return None,
        }
    }};
}

macro_rules! bind_vars {
    (
        $eval:expr,
        ($var:ident, $($vars:tt)*),
        ($arg:expr, $($args:tt)*)
    ) => {
        #[allow(unused)]
        let $var = $eval($arg);
        bind_vars!($eval, ($($vars)*), ($($args)*));
    };

    (
        $eval:expr,
        ($var:ident),
        ($($args:tt)*)
    ) => {
        bind_vars!($eval, ($var,), ($($args)*))
    };

    ($eval:expr, (), ()) => {};
}

macro_rules! apply_conds {
    (
        ($var:ident, $($vars:tt)*),
        (_, $($conds:tt)*)
    ) => {
        apply_conds!(($($vars)*), ($($conds)*))
    };

    (
        ($var:ident, $($vars:tt)*),
        ($cond:expr, $($conds:tt)*)
    ) => {
        $cond(&$var) && apply_conds!(($($vars)*), ($($conds)*))
    };

    (
        (),
        ()
    ) => {
        true
    };

    (
        ($var:ident),
        ($($conds:tt)*)
    ) => {
        apply_conds!(($var,), ($($conds)*))
    };

    (
        ($($vars:tt)*),
        ($($cond:tt)*)
    ) => {
        apply_conds!(($($vars)*), ($($cond)*,))
    };
}

fn is_zero(val: &Option<BigInt>) -> bool {
    val.as_ref().map_or(false, |i| i.is_zero())
}

fn is_one(val: &Option<BigInt>) -> bool {
    val.as_ref().map_or(false, |i| i.is_one())
}

fn is_all_ones<'a>(ty: Ty<'a>) -> impl FnOnce(&Option<BigInt>) -> bool + 'a {
    move |val| val == &Some(all_ones_value(ty))
}

fn all_ones_value(ty: Ty) -> BigInt {
    match *ty {
        TyKind::Uint(sz) => uint_max(sz),
        TyKind::Int(_) => BigInt::from(-1),
        _ => panic!("expected TyKind::Uint or TyKind::Int"),
    }
}

fn uint_max(sz: IntSize) -> BigInt {
    (BigInt::from(1) << sz.bits()) - 1
}

fn eval<'a>(
    e: &mut CachingEvaluator<'a, '_, eval::Public>,
    w: Wire<'a>,
) -> Option<BigInt> {
    e.eval_wire(w).and_then(Value::unwrap_single)
}

/// Like `try_const_fold`, but applies specific rules for certain cases where only some inputs are
/// known.
fn try_identities<'a>(
    c: &Circuit<'a>,
    ev: &mut CachingEvaluator<'a, '_, eval::Public>,
    gk: GateKind<'a>,
) -> Option<Wire<'a>> {
    let ty = gk.ty(c);
    Some(match gk {
        GateKind::Binary(op, a, b) => match_identities! {
            op, (a, b);
            vars (ac, bc);
            eval |w| eval(ev, w);
            // x + 0 = 0 + x = x
            BinOp::Add, (is_zero, _) => b,
            BinOp::Add, (_, is_zero) => a,
            // x - 0 = x
            BinOp::Sub, (_, is_zero) => a,
            // x - x = 0
            BinOp::Sub, (_, _) if a == b => c.lit(ty, 0),
            // 0 * x = x * 0 = 0
            BinOp::Mul, (is_zero, _) => c.lit(ty, 0),
            BinOp::Mul, (_, is_zero) => c.lit(ty, 0),
            // 1 * x = x * 1 = 1
            BinOp::Mul, (is_one, _) => b,
            BinOp::Mul, (_, is_one) => a,
            // 0 / x = 0
            BinOp::Div, (is_zero, _) => c.lit(ty, 0),
            // x / x = 1
            BinOp::Div, (_, _) if a == b => c.lit(ty, 1),
            // 0 % x = 0
            BinOp::Mod, (is_zero, _) => c.lit(ty, 0),
            // x % x = 0
            BinOp::Mod, (_, _) if a == b => c.lit(ty, 0),

            // 0 & x = x & 0 = 0
            BinOp::And, (is_zero, _) => c.lit(ty, 0),
            BinOp::And, (_, is_zero) => c.lit(ty, 0),
            // !0 & x = x & !0 = x
            BinOp::And, (is_all_ones(ty), _) => b,
            BinOp::And, (_, is_all_ones(ty)) => a,
            // x & x = x
            BinOp::And, (_, _) if a == b => a,

            // 0 | x = x | 0 = x
            BinOp::Or, (is_zero, _) => b,
            BinOp::Or, (_, is_zero) => a,
            // !0 | x = x | !0 = !0
            BinOp::Or, (is_all_ones(ty), _) => c.lit(ty, all_ones_value(ty)),
            BinOp::Or, (_, is_all_ones(ty)) => c.lit(ty, all_ones_value(ty)),
            // x | x = x
            BinOp::Or, (_, _) if a == b => a,

            // 0 ^ x = x ^ 0 = x
            BinOp::Xor, (is_zero, _) => b,
            BinOp::Xor, (_, is_zero) => a,
            // !0 ^ x = x ^ !0 = !x
            BinOp::Xor, (is_all_ones(ty), _) => c.not(b),
            BinOp::Xor, (_, is_all_ones(ty)) => c.not(a),
            // x ^ x = 0
            BinOp::Xor, (_, _) if a == b => c.lit(ty, 0),
        },
        GateKind::Shift(op, a, b) => match_identities! {
            op, (a, b);
            vars (ac, bc);
            eval |w| eval(ev, w);
            // x << 0 = x >> 0 = x
            ShiftOp::Shl, (_, is_zero) => a,
            ShiftOp::Shr, (_, is_zero) => a,
        },
        GateKind::Compare(op, a, b) => match_identities! {
            op, (a, b);
            vars (ac, bc);
            eval |w| eval(ev, w);
            // x == x, x <= x, x >= x: true
            CmpOp::Eq, (_, _) if a == b => c.lit(c.ty(TyKind::BOOL), 1),
            CmpOp::Le, (_, _) if a == b => c.lit(c.ty(TyKind::BOOL), 1),
            CmpOp::Ge, (_, _) if a == b => c.lit(c.ty(TyKind::BOOL), 1),
            // x != x, x < x, x > x: false
            CmpOp::Ne, (_, _) if a == b => c.lit(c.ty(TyKind::BOOL), 0),
            CmpOp::Gt, (_, _) if a == b => c.lit(c.ty(TyKind::BOOL), 0),
            CmpOp::Lt, (_, _) if a == b => c.lit(c.ty(TyKind::BOOL), 0),

            // (unsigned) x >= 0, 0 <= x: true
            CmpOp::Ge, (_, is_zero) if ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 1),
            CmpOp::Le, (is_zero, _) if ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 1),
            // (unsigned) x < 0, 0 > x: false
            CmpOp::Lt, (_, is_zero) if ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 0),
            CmpOp::Gt, (is_zero, _) if ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 0),
        },
        GateKind::Mux(c, t, e) => match_identities! {
            (), (c);
            vars (cc);
            eval |w| eval(ev, w);
            (), (is_zero) => e,
            (), (is_one) => e,
            (), (_) if t == e => t,
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
        match try_identities(c, &mut e, gk) {
            Some(w) => return w,
            None => {},
        }
        c.gate(gk)
    }
}

