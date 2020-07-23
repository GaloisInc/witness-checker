use crate::ir::circuit::{Circuit, Ty, Wire, GateKind, TyKind, IntSize, BinOp, ShiftOp, CmpOp};

// TODO: mod -> div + sub

pub fn compare_to_zero<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Compare(op, a, b) = gk {
        if a.ty.is_integer() {
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

pub fn mux<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Mux(cond, t, e) = gk {
        if t.ty.is_integer() {
            let mask = c.neg(c.cast(cond, t.ty));
            return c.or(c.and(mask, t), c.and(c.not(mask), e));
        }
    }
    c.gate(gk)
}


fn maybe_sign_extend(x: u64, ty: Ty) -> u64 {
    match *ty {
        TyKind::Uint(_sz) => x,
        TyKind::Int(sz) => {
            let y = x as i64;
            // Sign-extend to 64 bits
            let y = y << (64 - sz.bits()) >> (64 - sz.bits());
            y as u64
        },
        _ => panic!("expected Uint or Int, but got {:?}", ty),
    }
}

fn extend_integer_ty<'a>(c: &Circuit<'a>, ty: Ty) -> Ty<'a> {
    match *ty {
        TyKind::Uint(_) => c.ty(TyKind::U64),
        TyKind::Int(_) => c.ty(TyKind::I64),
        _ => panic!("expected Uint or Int, but got {:?}", ty),
    }
}

/// Normalize `w` to a valid 64-bit representation of `ty`.  For example, if `ty` is `U8`, then `w`
/// will be masked to retain only the lower 8 bits.
fn normalize_64<'a>(c: &Circuit<'a>, w: Wire<'a>, ty: Ty) -> Wire<'a> {
    let bits = ty.integer_size().bits();
    if bits >= 64 {
        return w;
    }
    match *ty {
        TyKind::Uint(_) => {
            let mask = !(!0_u64 << bits);
            c.and(w, c.lit(c.ty(TyKind::U64), mask))
        },
        TyKind::Int(_) => {
            let shift_amount = c.lit(c.ty(TyKind::U8), 64 - bits as u64);
            c.shr(c.shl(w, shift_amount), shift_amount)
        },
        _ => panic!("expected Uint or Int, but got {:?}", ty),
    }

}

/// Extend all integers to 64 bits.  That is, all `Uint`s will be extended to `U64`, and all `Int`s
/// will be extended to `I64`.
pub fn extend_to_64<'a>(c: &Circuit<'a>, old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if old.ty.is_integer() && old.ty.integer_size() != IntSize::I64 {
        match gk {
            GateKind::Lit(x, ty) => {
                return c.lit(extend_integer_ty(c, ty), maybe_sign_extend(x, ty));
            },
            GateKind::Secret(s) => {
                let new_ty = extend_integer_ty(c, s.ty);
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
                return normalize_64(c, c.gate(gk), old.ty);
            },
        }
    }
    c.gate(gk)
}

/// Convert all `Int`s to `Uint`s.
pub fn int_to_uint<'a>(c: &Circuit<'a>, old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    // Special handling for casts to and from Int types.  We look at `old` instead of `gk` here
    // because `gk`'s input wire has already been changed to an unsigned type.
    if let GateKind::Cast(old_w, old_dest_ty) = old.kind {
        // Casts from signed types require a sign extension.
        if let TyKind::Int(src_sz) = *old_w.ty {
            if old_dest_ty.is_integer() {
                let dest_sz = old_dest_ty.integer_size();
                if dest_sz.bits() > src_sz.bits() {
                    let new_dest_ty = c.ty(TyKind::Uint(dest_sz));
                    let cast = match gk {
                        GateKind::Cast(w, _ty) => c.cast(w, new_dest_ty),
                        _ => unreachable!(),
                    };

                    let sign_mask = c.lit(new_dest_ty, 1 << (src_sz.bits() - 1));
                    let sign = c.and(cast, sign_mask);
                    let sign_fill = c.neg(sign);
                    return c.or(cast, sign_fill);
                }
            }
        }

        // Casts from unsigned to signed only require a change to the destination type.  This case
        // is handled below.
    }

    if let TyKind::Int(sz) = *old.ty {
        let new_ty = c.ty(TyKind::Uint(sz));
        match gk {
            GateKind::Lit(x, _ty) => {
                return c.lit(new_ty, x);
            },
            GateKind::Secret(s) => {
                return c.new_secret(new_ty, s.val);
            },
            GateKind::Unary(_op, _a) => {},
            GateKind::Binary(op, a, b) => match op {
                // Note `Mul` returns only the lower half of the output, which is unaffected by
                // signedness of the inputs.
                BinOp::Add | BinOp::Sub | BinOp::Mul |
                BinOp::And | BinOp::Or | BinOp::Xor => {},
                BinOp::Div | BinOp::Mod => {
                    let a_neg = c.lt(a, c.lit(new_ty, 0));
                    let b_neg = c.lt(b, c.lit(new_ty, 0));
                    let a_abs = c.mux(a_neg, c.neg(a), a);
                    let b_abs = c.mux(b_neg, c.neg(b), b);
                    let r_abs = c.binary(op, a_abs, b_abs);
                    let r_neg = c.xor(a_neg, b_neg);
                    return c.mux(r_neg, c.neg(r_abs), r_abs);
                },
            },
            GateKind::Shift(op, a, b) => match op {
                ShiftOp::Shr => {
                    // Example: start with 0b10101010, shifting right by 2.
                    // - The logical shift result, 0b00101010, is missing the high 1 bits that
                    //   would be produced by sign extension.
                    // - Mask out the shifted sign bit, producing 0b00100000.  Negate: 0b11100000.
                    //   This fills in the missing high bits, but only when the sign bit is 1.
                    let sign_mask = c.lit(new_ty, 1 << (sz.bits() - 1));
                    let sign = c.and(a, sign_mask);
                    let sign_fill = c.neg(c.shr(sign, b));
                    return c.or(c.shr(a, b), sign_fill);
                },
                ShiftOp::Shl => {},
            },
            GateKind::Compare(op, a, b) => match op {
                CmpOp::Eq | CmpOp::Ne => {},
                CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => {
                    // Shift everything up by 2^(n-1). For 8-bit values, this maps  0..128 to
                    // 128..256 and maps -128..0 (= 128..256) to 0..128, so comparisons work.  The
                    // mapping amounts to just flipping the sign bit.
                    let sign_mask = c.lit(new_ty, 1 << (sz.bits() - 1));
                    return c.compare(op, c.xor(a, sign_mask), c.xor(b, sign_mask));
                },
            },
            GateKind::Mux(_, _, _) => {},
            // This covers only the case of casts *to* signed types.  Casts *from* signed types are
            // handled in the special case above.
            GateKind::Cast(w, _) => {
                return c.cast(w, new_ty);
            },
            GateKind::Pack(_) => {},
            // `Extract`'s input should already have had its output types changed.
            GateKind::Extract(_, _) => {},
            // TODO: need a way to handle gadgets whose output type is fixed or set internally.
            // (Gadgets whose output type matches an input should work fine, as all inputs have
            // already been changed to `Uint`.)
            GateKind::Gadget(_, _) => {},
        }
    }

    c.gate(gk)
}


/// Replace literals wider than 32 bits with combinations of multiple 32-bit literals.
pub fn reduce_lit_32<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Lit(x, ty) = gk {
        if x >> 32 != 0 {
            if let Some(w) = make_shifted_lit(c, x, ty) {
                return w;
            }
            if let Some(w) = make_shifted_lit(c, !x, ty) {
                return c.not(w);
            }
            return make_split_lit(c, x, ty);
        }
    }
    c.gate(gk)
}

fn make_shifted_lit<'a>(c: &Circuit<'a>, x: u64, ty: Ty<'a>) -> Option<Wire<'a>> {
    let shift = x.trailing_zeros();
    let y = x >> shift;
    if y >> 32 != 0 {
        // Too wide
        return None;
    }
    Some(c.shl(c.lit(ty, y), c.lit(c.ty(TyKind::U8), shift as u64)))
}

fn make_split_lit<'a>(c: &Circuit<'a>, x: u64, ty: Ty<'a>) -> Wire<'a> {
    c.or(
        c.shl(c.lit(ty, x >> 32), c.lit(c.ty(TyKind::U8), 32)),
        c.lit(ty, x & ((1 << 32) - 1)),
    )
}
