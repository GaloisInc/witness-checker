use num_bigint::BigInt;
use num_traits::{Zero, One};
use crate::eval::{self, LiteralEvaluator, Evaluator, Value};
use crate::ir::circuit::{
    CircuitTrait, CircuitExt, CircuitBase, CircuitFilter, CircuitRef, DynCircuitRef, Ty, Wire,
    GateKind, TyKind, IntSize, BinOp, ShiftOp, CmpOp,
};
use crate::ir::migrate::{self, Migrate};

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

/// Returns `true` if `val` is definitely nonzero.
///
/// This is not the same as `!is_zero(val)`, which returns `true` when `val` is *possibly* nonzero.
fn is_non_zero(val: &Option<BigInt>) -> bool {
    val.as_ref().map_or(false, |i| !i.is_zero())
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
    c: &impl CircuitTrait<'a>,
    e: &mut impl Evaluator<'a>,
    w: Wire<'a>,
) -> Option<BigInt> {
    e.eval_wire(c, w).ok().and_then(Value::unwrap_single)
}

fn const_foldable(gk: GateKind) -> bool {
    match gk {
        GateKind::Lit(..) => false,
        GateKind::Secret(..) => false,
        GateKind::Erased(..) => false,
        GateKind::Argument(..) => false,
        GateKind::Unary(_, a) => a.is_lit(),
        GateKind::Binary(_, a, b) => a.is_lit() && b.is_lit(),
        GateKind::Shift(_, a, b) => a.is_lit() && b.is_lit(),
        GateKind::Compare(_, a, b) => a.is_lit() && b.is_lit(),
        GateKind::Mux(c, t, e) => c.is_lit() && t.is_lit() && e.is_lit(),
        GateKind::Cast(a, _) => a.is_lit(),
        // `Pack` can't be folded to a `Lit`, since `Lit` can't have bundle type.
        GateKind::Pack(..) => false,
        // `Extract` can't be folded because its input can't be a `Lit`.
        GateKind::Extract(..) => false,
        GateKind::Gadget(_, ws) => ws.iter().all(|&w| w.is_lit()),
        GateKind::Call(c) => c.args.iter().all(|&w| w.is_lit()),
    }
}

/// If `gk`'s inputs are all literals, evaluate it to produce another literal.
fn try_const_fold<'a>(
    c: &impl CircuitTrait<'a>,
    gk: GateKind<'a>,
) -> Option<Wire<'a>> {
    if !const_foldable(gk) {
        return None;
    }

    let ty = gk.ty(c);
    let val = eval::eval_gate_public(c.as_base(), ty, gk)?;
    let i = val.as_single()?;
    Some(c.lit(ty, i))
}

fn wire_eq<'a>(a: Wire<'a>, b: Wire<'a>) -> bool {
    if a == b {
        return true;
    }

    match (a.kind, b.kind) {
        (GateKind::Lit(a_bits, a_ty), GateKind::Lit(b_bits, b_ty)) => {
            a_bits == b_bits && a_ty == b_ty
        },
        _ => false,
    }
}

/// Like `try_const_fold`, but applies specific rules for certain cases where only some inputs are
/// known.
fn try_identities<'a>(
    c: &impl CircuitTrait<'a>,
    ev: &mut impl Evaluator<'a>,
    gk: GateKind<'a>,
) -> Option<Wire<'a>> {
    let ty = gk.ty(c);
    Some(match gk {
        GateKind::Binary(op, a, b) => match_identities! {
            op, (a, b);
            vars (ac, bc);
            eval |w| eval(c, ev, w);
            // x + 0 = 0 + x = x
            BinOp::Add, (is_zero, _) => b,
            BinOp::Add, (_, is_zero) => a,
            // x - 0 = x
            BinOp::Sub, (_, is_zero) => a,
            // x - x = 0
            BinOp::Sub, (_, _) if wire_eq(a, b) => c.lit(ty, 0),
            // 0 * x = x * 0 = 0
            BinOp::Mul, (is_zero, _) => c.lit(ty, 0),
            BinOp::Mul, (_, is_zero) => c.lit(ty, 0),
            // 1 * x = x * 1 = 1
            BinOp::Mul, (is_one, _) => b,
            BinOp::Mul, (_, is_one) => a,
            // 0 / x = 0
            BinOp::Div, (is_zero, _) => c.lit(ty, 0),
            // x / 1 = x
            BinOp::Div, (_, is_one) => a,
            // x / x = 1  (x must be nonzero, since we define 0 / 0 = 0)
            BinOp::Div, (_, is_non_zero) if wire_eq(a, b) => c.lit(ty, 1),
            // 0 % x = 0
            BinOp::Mod, (is_zero, _) => c.lit(ty, 0),
            // x % 1 = 0
            BinOp::Mod, (_, is_one) => c.lit(ty, 0),
            // x % x = 0  (applies even when x is zero, since we define 0 % 0 = 0)
            BinOp::Mod, (_, is_non_zero) if wire_eq(a, b) => c.lit(ty, 0),

            // 0 & x = x & 0 = 0
            BinOp::And, (is_zero, _) => c.lit(ty, 0),
            BinOp::And, (_, is_zero) => c.lit(ty, 0),
            // !0 & x = x & !0 = x
            BinOp::And, (is_all_ones(ty), _) => b,
            BinOp::And, (_, is_all_ones(ty)) => a,
            // x & x = x
            BinOp::And, (_, _) if wire_eq(a, b) => a,

            // 0 | x = x | 0 = x
            BinOp::Or, (is_zero, _) => b,
            BinOp::Or, (_, is_zero) => a,
            // !0 | x = x | !0 = !0
            BinOp::Or, (is_all_ones(ty), _) => c.lit(ty, all_ones_value(ty)),
            BinOp::Or, (_, is_all_ones(ty)) => c.lit(ty, all_ones_value(ty)),
            // x | x = x
            BinOp::Or, (_, _) if wire_eq(a, b) => a,

            // 0 ^ x = x ^ 0 = x
            BinOp::Xor, (is_zero, _) => b,
            BinOp::Xor, (_, is_zero) => a,
            // !0 ^ x = x ^ !0 = !x
            BinOp::Xor, (is_all_ones(ty), _) => c.not(b),
            BinOp::Xor, (_, is_all_ones(ty)) => c.not(a),
            // x ^ x = 0
            BinOp::Xor, (_, _) if wire_eq(a, b) => c.lit(ty, 0),
        },
        GateKind::Shift(op, a, b) => match_identities! {
            op, (a, b);
            vars (ac, bc);
            eval |w| eval(c, ev, w);
            // x << 0 = x >> 0 = x
            ShiftOp::Shl, (_, is_zero) => a,
            ShiftOp::Shr, (_, is_zero) => a,
        },
        GateKind::Compare(op, a, b) => match_identities! {
            op, (a, b);
            vars (ac, bc);
            eval |w| eval(c, ev, w);
            // x == x, x <= x, x >= x: true
            CmpOp::Eq, (_, _) if wire_eq(a, b) => c.lit(c.ty(TyKind::BOOL), 1),
            CmpOp::Le, (_, _) if wire_eq(a, b) => c.lit(c.ty(TyKind::BOOL), 1),
            CmpOp::Ge, (_, _) if wire_eq(a, b) => c.lit(c.ty(TyKind::BOOL), 1),
            // x != x, x < x, x > x: false
            CmpOp::Ne, (_, _) if wire_eq(a, b) => c.lit(c.ty(TyKind::BOOL), 0),
            CmpOp::Gt, (_, _) if wire_eq(a, b) => c.lit(c.ty(TyKind::BOOL), 0),
            CmpOp::Lt, (_, _) if wire_eq(a, b) => c.lit(c.ty(TyKind::BOOL), 0),

            // (unsigned) x >= 0, 0 <= x: true
            CmpOp::Ge, (_, is_zero) if a.ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 1),
            CmpOp::Le, (is_zero, _) if a.ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 1),
            // (unsigned) x < 0, 0 > x: false
            CmpOp::Lt, (_, is_zero) if a.ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 0),
            CmpOp::Gt, (is_zero, _) if a.ty.is_uint() => c.lit(c.ty(TyKind::BOOL), 0),
        },
        GateKind::Mux(c_, t, e) => match_identities! {
            (), (c_);
            vars (cc);
            eval |w| eval(c, ev, w);
            (), (is_zero) => e,
            (), (is_one) => t,
            (), (_) if wire_eq(t, e) => t,
        },

        _ => return None,
    })
}

/// Try to apply more specialized identities that don't fit into the `match_identities!` framework.
fn try_identities2<'a>(
    c: &impl CircuitTrait<'a>,
    ev: &mut impl Evaluator<'a>,
    gk: GateKind<'a>,
) -> Option<Wire<'a>> {
    macro_rules! call {
        ($func:ident) => {
            if let Some(w) = $func(c, ev, gk) {
                return Some(w);
            }
        };
    }
    call!(try_identity_compare_mux);
    None
}

macro_rules! match_gate_kind {
    ($gk:expr, $Variant:ident($($arg:ident),*)) => {
        match $gk {
            GateKind::$Variant($($arg,)*) => Some(($($arg),*)),
            _ => None,
        }
    };
}

macro_rules! guard {
    ($cond:expr) => {
        if !$cond {
            return None;
        }
    };
}

/// Examine a comparison between two mux trees, where each leaf of the tree is a constant.
/// Replaces the comparison with a constant if every left constant compared with every right
/// constant produces the same outcome.  For example, `{1, 2} < {3, 4, 5}` would be replaced with
/// true.
fn try_identity_compare_mux<'a>(
    c: &impl CircuitTrait<'a>,
    ev: &mut impl Evaluator<'a>,
    gk: GateKind<'a>,
) -> Option<Wire<'a>> {
    let (op, a, b) = match_gate_kind!(gk, Compare(op, a, b))?;
    guard!(matches!(a.kind, GateKind::Lit(..) | GateKind::Mux(..)));
    guard!(matches!(b.kind, GateKind::Lit(..) | GateKind::Mux(..)));

    fn gather_mux_leaves<'a>(
        c: &impl CircuitTrait<'a>,
        ev: &mut impl Evaluator<'a>,
        w: Wire<'a>,
        out: &mut Vec<BigInt>,
    ) -> bool {
        match w.kind {
            GateKind::Mux(_, t, e) => {
                gather_mux_leaves(c, ev, t, out) && gather_mux_leaves(c, ev, e, out)
            },
            _ => match eval(c, ev, w) {
                Some(x) => {
                    out.push(x);
                    true
                },
                None => {
                    false
                },
            },
        }
    }
    let mut a_vals = Vec::new();
    let mut b_vals = Vec::new();
    guard!(gather_mux_leaves(c, ev, a, &mut a_vals));
    guard!(gather_mux_leaves(c, ev, b, &mut b_vals));

    let mut all_true = true;
    let mut all_false = true;
    for av in &a_vals {
        for bv in &b_vals {
            let result = match op {
                CmpOp::Eq => av == bv,
                CmpOp::Ne => av != bv,
                CmpOp::Lt => av < bv,
                CmpOp::Le => av <= bv,
                CmpOp::Gt => av > bv,
                CmpOp::Ge => av >= bv,
            };
            if result {
                all_false = false;
            } else {
                all_true = false;
            }
            if !all_true && !all_false {
                return None;
            }
        }
    }

    let const_val =
        if all_true { 1 }
        else if all_false { 0 }
        else { unreachable!() };
    Some(c.lit(c.ty(TyKind::BOOL), const_val))
}

pub struct ConstFold<F>(pub F);

impl<'a, F: CircuitFilter<'a> + 'a> CircuitFilter<'a> for ConstFold<F>
where F: Migrate<'a, 'a, Output = F> {
    circuit_filter_common_methods!();

    fn gate(&self, base: &CircuitBase<'a>, gk: GateKind<'a>) -> Wire<'a> {
        if let GateKind::Gadget(k, ws) = gk {
            if ws.iter().all(|w| w.is_lit()) {
                // All inputs are literals, so the gadget should be constant-foldable.  It's
                // technically possible for a gadget to include fresh secrets, but so far that
                // hasn't been useful for anything.
                //
                // Note we pass `self` instead of `self.0`, so the decomposed gates will be
                // recursively constant-folded.
                let c: DynCircuitRef = CircuitRef { base, filter: self };
                return k.decompose(c, ws);
            }
        }

        let c = CircuitRef { base, filter: &self.0 };
        if let Some(w) = try_const_fold(&c, gk) {
            return w;
        }
        if let Some(w) = try_identities(&c, &mut LiteralEvaluator, gk) {
            return w;
        }
        if let Some(w) = try_identities2(&c, &mut LiteralEvaluator, gk) {
            return w;
        }
        c.gate(gk)
    }
}

impl<'a, 'b, F> Migrate<'a, 'b> for ConstFold<F>
where
    F: Migrate<'a, 'b>,
{
    type Output = ConstFold<F::Output>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        ConstFold(v.visit(self.0))
    }
}
