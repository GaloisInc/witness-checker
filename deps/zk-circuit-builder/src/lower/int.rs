use std::convert::TryFrom;
use num_bigint::BigUint;
use num_traits::Zero;

use crate::ir::circuit::{
    CircuitTrait, CircuitExt, CircuitRef, CircuitFilter, Ty, Wire, GateKind, TyKind, IntSize,
    BinOp, ShiftOp, CmpOp,
};

// TODO: mod -> div + sub

pub fn compare_to_zero<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    if let GateKind::Compare(op, a, b) = gk {
        if a.ty.is_integer() && *a.ty != TyKind::BOOL {
            let zero = c.lit(a.ty, 0);

            // For Lt/Gt comparisons, we have to extend the inputs by 1 bit, then do a signed
            // comparison (regardless of input signedness).
            //
            // Signed case: consider 8-bit inputs `-128 < 1` (true).  This becomes `-128 - 1 < 0`,
            // but `-128 - 1` underflows to `127`, and `127 < 0` is false.  But if the inputs are
            // first extended to 9 bits, then `-128 - 1 = -129`, and `-129 < 0` is true.
            //
            // Unsigned case: `x < 0` is always false for unsigned `x`.
            //
            // These are all lazy evaluated.
            let ext_ty = c.ty(TyKind::Int(IntSize(a.ty.integer_size().bits() + 1)));
            let ext_zero = c.lit(ext_ty, 0);
            let ext = |w| c.cast(w, ext_ty);

            return match op {
                CmpOp::Eq => c.eq(c.sub(a, b), zero),
                CmpOp::Ne => c.not(c.eq(c.sub(a, b), zero)),
                CmpOp::Lt => c.lt(c.sub(ext(a), ext(b)), ext_zero),
                CmpOp::Le => c.not(c.lt(c.sub(ext(b), ext(a)), ext_zero)),
                CmpOp::Gt => c.lt(c.sub(ext(b), ext(a)), ext_zero),
                CmpOp::Ge => c.not(c.lt(c.sub(ext(a), ext(b)), ext_zero)),
            };
        }
    }
    c.gate(gk)
}

pub fn compare_to_greater_or_equal_to_zero<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    if let GateKind::Compare(op, a, b) = gk {
        if a.ty.is_integer() && *a.ty != TyKind::BOOL {
            let zero = c.lit(a.ty, 0);
            let ext_ty = c.ty(TyKind::Int(IntSize(a.ty.integer_size().bits() + 1)));
            let ext_zero = c.lit(ext_ty, 0);
            let ext = |w| c.cast(w, ext_ty);
            return match op {
                CmpOp::Eq => c.eq(c.sub(a, b), zero),
                CmpOp::Ne => c.not(c.eq(c.sub(a, b), zero)),
                // Greater or equal: a - b >= 0.
                CmpOp::Ge => c.ge(c.sub(ext(a), ext(b)), ext_zero),
                // Lesser or equal: swap a and b.
                CmpOp::Le => c.ge(c.sub(ext(b), ext(a)), ext_zero),
                // Lesser than: not greater or equal.
                CmpOp::Lt => c.not(c.ge(c.sub(ext(a), ext(b)), ext_zero)),
                // Greater or equal: not lesser or equal.
                CmpOp::Gt => c.not(c.ge(c.sub(ext(b), ext(a)), ext_zero)),
            };
        }
    }
    c.gate(gk)
}

pub fn mux<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    if let GateKind::Mux(cond, t, e) = gk {
        if t.ty.is_integer() {
            let mask = c.neg(c.cast(cond, t.ty));
            return c.or(c.and(mask, t), c.and(c.not(mask), e));
        }
    }
    c.gate(gk)
}


/// Replace `Mod` gates with a circuit using `Div`, `Mul`, and `Sub`.  Useful for SCALE, which does
/// not support `Mod`.
pub fn mod_to_div<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    if let GateKind::Binary(BinOp::Mod, x, y) = gk {
        // FIXME: changes behavior on division by zero (returns `x` for `x % 0`, not `0`)
        return c.sub(
            x,
            c.mul(c.div(x, y), y),
        );
    }
    c.gate(gk)
}


/// Replace any shift by a non-constant with a series of shifts by constants.  Useful for SCALE,
/// which supports only constant shifts.
pub fn non_constant_shift<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    if let GateKind::Shift(op, x, amt) = gk {
        // Shifts by a constant are allowed.
        if let GateKind::Lit(_, _) = amt.kind {
            return c.gate(gk);
        }

        // The width of the input `x`.
        let width = x.ty.integer_size().bits();
        // The number of bits in the shift amount, or the base-2 log of `width`.
        let bits = width.trailing_zeros();
        assert!(1 << bits == width);
        let ty_u8 = c.ty(TyKind::U8);
        let mut y = x;
        for i in 0..bits {
            // If bit `i` is set, then shift by `1 << i`.
            let amt_bit = c.lit(ty_u8, 1 << i);
            let bit_set = c.ne(c.lit(ty_u8, 0), c.and(amt, amt_bit));
            y = c.mux(bit_set, c.shift(op, y, amt_bit), y);
        }
        // If bits beyond `level` are set, then shift by `1 << level`.
        let width_val = c.lit(ty_u8, width as u64);
        let overflowed = c.ge(amt, width_val);
        y = c.mux(overflowed, c.shift(op, y, width_val), y);

        return y;
    }
    c.gate(gk)
}
