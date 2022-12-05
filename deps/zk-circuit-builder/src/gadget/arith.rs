use num_bigint::{BigInt, BigUint};
use crate::eval::{Value, EvalResult};
use crate::ir::circuit::{
    CircuitExt, CircuitBase, DynCircuitRef, Wire, Ty, TyKind, IntSize, GadgetKind, GadgetKindRef,
};
use crate::ir::typed::{Builder, AsBuilder, Repr, TWire};


fn overflow_result(ty: Ty, raw: BigInt) -> Value {
    let v = Value::trunc(ty, raw.clone());
    let overflowed = v.as_single().unwrap() != &raw;
    Value::Bundle(vec![v, Value::trunc(Ty::bool(), BigInt::from(overflowed as u32))])
}


/// Add two unsigned integers and check for overflow.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct AddWithOverflow;
impl_gadget_kind_support!(AddWithOverflow);

impl<'a> GadgetKind<'a> for AddWithOverflow {
    fn transfer<'b>(&self, c: &CircuitBase<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &CircuitBase<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        assert!(arg_tys.len() == 2, "expected exactly 2 arguments");
        assert!(arg_tys[0] == arg_tys[1], "type mismatch: {:?} != {:?}", arg_tys[0], arg_tys[1]);
        let ty = arg_tys[0];
        match *ty {
            TyKind::Uint(_) => {},
            _ => panic!("expected Uint, but got {:?}", ty),
        }

        c.ty_bundle(&[ty, c.ty(TyKind::BOOL)])
    }

    fn decompose(&self, c: DynCircuitRef<'a, '_>, args: &[Wire<'a>]) -> Wire<'a> {
        let sum = c.add(args[0], args[1]);
        let overflow = c.lt(sum, args[0]);
        c.pack(&[sum, overflow])
    }

    fn eval(&self, arg_tys: &[Ty<'a>], args: &[EvalResult<'a>]) -> EvalResult<'a> {
        let a = args[0].as_ref()?.as_single().unwrap();
        let b = args[1].as_ref()?.as_single().unwrap();
        Ok(overflow_result(arg_tys[0], a + b))
    }
}

/// Subtract two unsigned integers and check for overflow.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SubWithOverflow;
impl_gadget_kind_support!(SubWithOverflow);

impl<'a> GadgetKind<'a> for SubWithOverflow {
    fn transfer<'b>(&self, c: &CircuitBase<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &CircuitBase<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        assert!(arg_tys.len() == 2, "expected exactly 2 arguments");
        assert!(arg_tys[0] == arg_tys[1], "type mismatch: {:?} != {:?}", arg_tys[0], arg_tys[1]);
        let ty = arg_tys[0];
        match *ty {
            TyKind::Uint(_) => {},
            _ => panic!("expected Uint, but got {:?}", ty),
        }

        c.ty_bundle(&[ty, c.ty(TyKind::BOOL)])
    }

    fn decompose(&self, c: DynCircuitRef<'a, '_>, args: &[Wire<'a>]) -> Wire<'a> {
        let diff = c.sub(args[0], args[1]);
        let overflow = c.gt(diff, args[0]);
        c.pack(&[diff, overflow])
    }

    fn eval(&self, arg_tys: &[Ty<'a>], args: &[EvalResult<'a>]) -> EvalResult<'a> {
        let a = args[0].as_ref()?.as_single().unwrap();
        let b = args[1].as_ref()?.as_single().unwrap();
        Ok(overflow_result(arg_tys[0], a - b))
    }
}

/// Perform double-word multiplication (for example, a `32 x 32 -> 64` bit multiply).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct WideMul;
impl_gadget_kind_support!(WideMul);

impl<'a> GadgetKind<'a> for WideMul {
    fn transfer<'b>(&self, c: &CircuitBase<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &CircuitBase<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        assert!(arg_tys.len() == 2, "expected exactly 2 arguments");
        assert!(arg_tys[0] == arg_tys[1], "type mismatch: {:?} != {:?}", arg_tys[0], arg_tys[1]);
        let ty = arg_tys[0];
        let low_ty = match *ty {
            TyKind::Uint(sz) | TyKind::Int(sz) => c.ty(TyKind::Uint(sz)),
            _ => panic!("expected Uint or Int, but got {:?}", ty),
        };

        c.ty_bundle(&[low_ty, ty])
    }

    fn decompose(&self, c: DynCircuitRef<'a, '_>, args: &[Wire<'a>]) -> Wire<'a> {
        let ty = args[0].ty;
        let (sz, signed) = match *ty {
            TyKind::Uint(sz) => (sz, false),
            TyKind::Int(sz) => (sz, true),
            _ => unreachable!(),
        };
        let uty = c.ty(TyKind::Uint(sz));

        // Build a signed or unsigned `N x N -> 2N` multiplier, given only an `N x N -> N` multiply
        // gate (like the one SCALE provides).
        //
        // Pseudocode:
        //
        //      a0 = low_half(a)
        //      a1 = high_half(a)
        //      b0 = low_half(b)
        //      b1 = high_half(b)
        //
        //      c0, carry = (a0 * b0) + ((a0 * b1) << (N/2)) + ((a1 * b0) << (N/2))
        //      c1 = ((a0 * b1 + a1 * b0) >> (N/2)) + (a1 * b1) + carry
        //      if signed:
        //          if a < 0:
        //              c1 -= b
        //          if b < 0:
        //              c1 -= a
        //
        //      return c0, c1

        assert!(sz.bits() % 2 == 0, "WideMul for odd-sized integers is not yet supported");
        let mask_val = (BigUint::from(1_u8) << (sz.bits() / 2)) - 1_u8;
        let mask = c.lit(ty, mask_val);
        let half_n = c.lit(c.ty(TyKind::U8), sz.bits() as u64 / 2);
        let zero = c.lit(ty, 0);

        let a = args[0];
        let b = args[1];
        let a0 = c.and(a, mask);
        let a1 = c.and(c.shr(a, half_n), mask);
        let b0 = c.and(b, mask);
        let b1 = c.and(c.shr(b, half_n), mask);

        // Compute the low output, c0 = a0 * b0 + a0 * b1 << (N/2) + a1 * b0 << (N/2).  Also
        // computes the carries from the two additions, so they can be added to the high word.
        let g_add_with_overflow = c.intern_gadget_kind(AddWithOverflow);

        let sum1_carry1 = c.gadget(
            g_add_with_overflow,
            &[
                c.shl(c.cast(c.mul(a0, b1), uty), half_n),
                c.shl(c.cast(c.mul(a1, b0), uty), half_n),
            ],
        );
        let sum1 = c.extract(sum1_carry1, 0);
        let carry1 = c.extract(sum1_carry1, 1);

        let sum2_carry2 = c.gadget(
            g_add_with_overflow,
            &[
                sum1,
                c.cast(c.mul(a0, b0), uty),
            ],
        );
        let sum2 = c.extract(sum2_carry2, 0);
        let carry2 = c.extract(sum2_carry2, 1);

        let c0 = sum2;
        let carry = c.add(c.cast(carry1, ty), c.cast(carry2, ty));

        // Compute the high output, c1 = a1 * b1 + a0 * b1 >> (N/2) + a1 * b0 >> (N/2) + carry.
        let a0b1_high = if signed {
            c.and(c.shr(c.mul(a0, b1), half_n), mask)
        } else {
            c.shr(c.mul(a0, b1), half_n)
        };
        let a1b0_high = if signed {
            c.and(c.shr(c.mul(a1, b0), half_n), mask)
        } else {
            c.shr(c.mul(a1, b0), half_n)
        };
        let sum = c.add(a0b1_high, a1b0_high);
        let sum = c.add(sum, c.mul(a1, b1));
        let sum = c.add(sum, carry);

        let c1 = if signed {
            let adj1 = c.mux(c.lt(a, zero), b, zero);
            let adj2 = c.mux(c.lt(b, zero), a, zero);
            c.sub(c.sub(sum, adj1), adj2)
        } else {
            sum
        };


        c.pack(&[c0, c1])
    }

    fn eval(&self, arg_tys: &[Ty<'a>], args: &[EvalResult<'a>]) -> EvalResult<'a> {
        let sz = arg_tys[0].integer_size();
        let a = args[0].as_ref()?.as_single().unwrap();
        let b = args[1].as_ref()?.as_single().unwrap();
        let product = a * b;
        let low = Value::SingleInteger(&product & ((BigInt::from(1) << sz.bits()) - 1));
        let high = Value::trunc(arg_tys[0], product >> sz.bits());
        Ok(Value::Bundle(vec![low, high]))
    }
}


/// Perform double-word multiplication (for example, a `32 x 32 -> 64` bit multiply).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct WideMul2;
impl_gadget_kind_support!(WideMul2);

impl<'a> GadgetKind<'a> for WideMul2 {
    fn transfer<'b>(&self, c: &CircuitBase<'b>) -> GadgetKindRef<'b> {
        c.intern_gadget_kind(self.clone())
    }

    fn typecheck(&self, c: &CircuitBase<'a>, arg_tys: &[Ty<'a>]) -> Ty<'a> {
        assert!(arg_tys.len() == 2, "expected exactly 2 arguments");
        let (a_sz, a_sign) = match *arg_tys[0] {
            TyKind::Uint(sz) => (sz, false),
            TyKind::Int(sz) => (sz, true),
            _ => panic!("expected Uint or Int, but got {:?}", arg_tys[0]),
        };
        let (b_sz, b_sign) = match *arg_tys[1] {
            TyKind::Uint(sz) => (sz, false),
            TyKind::Int(sz) => (sz, true),
            _ => panic!("expected Uint or Int, but got {:?}", arg_tys[1]),
        };
        assert_eq!(a_sz, b_sz, "WideMul inputs must have the same width");

        if a_sign || b_sign {
            c.ty(TyKind::Int(IntSize(a_sz.bits() * 2)))
        } else {
            c.ty(TyKind::Uint(IntSize(a_sz.bits() * 2)))
        }
    }

    fn decompose(&self, c: DynCircuitRef<'a, '_>, args: &[Wire<'a>]) -> Wire<'a> {
        let (x_sz, x_sign) = match *args[0].ty {
            TyKind::Uint(sz) => (sz, false),
            TyKind::Int(sz) => (sz, true),
            _ => panic!("expected Uint or Int, but got {:?}", args[0].ty),
        };
        let (y_sz, y_sign) = match *args[1].ty {
            TyKind::Uint(sz) => (sz, false),
            TyKind::Int(sz) => (sz, true),
            _ => panic!("expected Uint or Int, but got {:?}", args[1].ty),
        };
        debug_assert_eq!(x_sz, y_sz, "WideMul inputs must have the same width");
        let sz = x_sz;
        let sign = x_sign || y_sign;

        let sz_round_up = IntSize((sz.bits() + 1) & !1);
        let sz_double = IntSize(sz.bits() * 2);

        let uty = c.ty(TyKind::Uint(sz_round_up));
        let ity = c.ty(TyKind::Int(sz_round_up));
        let out_ty = if sign {
            c.ty(TyKind::Int(sz_double))
        } else {
            c.ty(TyKind::Uint(sz_double))
        };

        let n = sz.bits();
        let m = (sz.bits() + 1) / 2;
        assert!(n <= 255);

        let x = args[0];
        let y = args[1];

        let x0 = c.and(c.cast(x, uty), c.lit(uty, (BigUint::from(1_u8) << m) - 1_u8));
        // Cast after shift so the sign extension takes effect.
        let x1 = c.cast(c.shr(x, c.lit(Ty::uint(8), m)), uty);
        let y0 = c.and(c.cast(y, uty), c.lit(uty, (BigUint::from(1_u8) << m) - 1_u8));
        let y1 = c.cast(c.shr(y, c.lit(Ty::uint(8), m)), uty);

        let z2 = c.mul(x1, y1);
        let z1 = {
            // In each product, sign-extend if the high (1) operand of the input is signed.
            let x0y1 = if y_sign {
                c.cast(c.cast(c.mul(x0, y1), ity), out_ty)
            } else {
                c.cast(c.mul(x0, y1), out_ty)
            };
            let x1y0 = if x_sign {
                c.cast(c.cast(c.mul(x1, y0), ity), out_ty)
            } else {
                c.cast(c.mul(x1, y0), out_ty)
            };
            c.add(x0y1, x1y0)
        };
        let z0 = c.mul(x0, y0);

        let out = c.add(c.add(
                c.cast(z0, out_ty),
                c.shl(c.cast(z1, out_ty), c.lit(Ty::uint(8), m)),
            ),
            c.shl(c.cast(z2, out_ty), c.lit(Ty::uint(8), 2 * m)),
        );

        out
    }

    fn eval(&self, arg_tys: &[Ty<'a>], args: &[EvalResult<'a>]) -> EvalResult<'a> {
        let sz = arg_tys[0].integer_size();
        let a = args[0].as_ref()?.as_single().unwrap();
        let b = args[1].as_ref()?.as_single().unwrap();
        let product = a * b;
        Ok(Value::SingleInteger(product))
    }
}


pub trait BuilderExt<'a>: AsBuilder<'a> {
    fn add_with_overflow<A: AddWithOverflowTrait<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> (TWire<'a, A::Output>, TWire<'a, bool>) {
        let (result, overflow) = <A as AddWithOverflowTrait<B>>::add_with_overflow(
            self.as_builder(),
            a.repr,
            b.repr,
        );
        (TWire::new(result), TWire::new(overflow))
    }

    fn sub_with_overflow<A: SubWithOverflowTrait<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> (TWire<'a, A::Output>, TWire<'a, bool>) {
        let (result, overflow) = <A as SubWithOverflowTrait<B>>::sub_with_overflow(
            self.as_builder(),
            a.repr,
            b.repr,
        );
        (TWire::new(result), TWire::new(overflow))
    }

    fn wide_mul<A: WideMulTrait<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as WideMulTrait<B>>::wide_mul(
            self.as_builder(),
            a.repr,
            b.repr,
        ))
    }
}

impl<'a> BuilderExt<'a> for Builder<'a> {}


pub trait AddWithOverflowTrait<'a, Other = Self>
where Self: Repr<'a>, Other: Repr<'a> {
    type Output: Repr<'a>;
    fn add_with_overflow(
        bld: &Builder<'a>,
        a: Self::Repr,
        b: Other::Repr,
    ) -> (<Self::Output as Repr<'a>>::Repr, <bool as Repr<'a>>::Repr);
}

impl<'a> AddWithOverflowTrait<'a> for u64 {
    type Output = u64;
    fn add_with_overflow(
        bld: &Builder<'a>,
        a: Wire<'a>,
        b: Wire<'a>,
    ) -> (Wire<'a>, Wire<'a>) {
        let c = bld.circuit();
        let g = c.intern_gadget_kind(AddWithOverflow);
        let out = c.gadget(g, &[a, b]);
        (c.extract(out, 0), c.extract(out, 1))
    }
}


pub trait SubWithOverflowTrait<'a, Other = Self>
where Self: Repr<'a>, Other: Repr<'a> {
    type Output: Repr<'a>;
    fn sub_with_overflow(
        bld: &Builder<'a>,
        a: Self::Repr,
        b: Other::Repr,
    ) -> (<Self::Output as Repr<'a>>::Repr, <bool as Repr<'a>>::Repr);
}

impl<'a> SubWithOverflowTrait<'a> for u64 {
    type Output = u64;
    fn sub_with_overflow(
        bld: &Builder<'a>,
        a: Wire<'a>,
        b: Wire<'a>,
    ) -> (Wire<'a>, Wire<'a>) {
        let c = bld.circuit();
        let g = c.intern_gadget_kind(SubWithOverflow);
        let out = c.gadget(g, &[a, b]);
        (c.extract(out, 0), c.extract(out, 1))
    }
}


pub trait WideMulTrait<'a, Other = Self>
where Self: Repr<'a>, Other: Repr<'a> {
    type Output: Repr<'a>;
    fn wide_mul(
        bld: &Builder<'a>,
        a: Self::Repr,
        b: Other::Repr,
    ) -> <Self::Output as Repr<'a>>::Repr;
}

impl<'a> WideMulTrait<'a> for u64 {
    type Output = (u64, u64);
    fn wide_mul(
        bld: &Builder<'a>,
        a: Wire<'a>,
        b: Wire<'a>,
    ) -> (TWire<'a, u64>, TWire<'a, u64>) {
        let c = bld.circuit();
        let g = c.intern_gadget_kind(WideMul);
        let out = c.gadget(g, &[a, b]);
        (TWire::new(c.extract(out, 0)), TWire::new(c.extract(out, 1)))
    }
}

impl<'a> WideMulTrait<'a> for i64 {
    type Output = (u64, i64);
    fn wide_mul(
        bld: &Builder<'a>,
        a: Wire<'a>,
        b: Wire<'a>,
    ) -> (TWire<'a, u64>, TWire<'a, i64>) {
        let c = bld.circuit();
        let g = c.intern_gadget_kind(WideMul);
        let out = c.gadget(g, &[a, b]);
        (TWire::new(c.extract(out, 0)), TWire::new(c.extract(out, 1)))
    }
}


#[cfg(test)]
mod test {
    use crate::eval;
    use crate::ir::circuit::{Circuit, FilterNil, Arenas};
    use crate::lower::gadget::DecomposeGadgets;
    use super::*;

    fn wide_mul2_common(a_ty: TyKind<'static>, b_ty: TyKind<'static>) {
        // We use two separate, unrelated lifetimes for the two circuit arenas to ensure that wires
        // for the two circuits can't be mixed up.
        fn inner<'a, 'b>(
            arenas1: &'a Arenas,
            arenas2: &'b Arenas,
            a_ty: TyKind<'static>,
            b_ty: TyKind<'static>,
        ) {
            let c1 = Circuit::new(arenas1, true, FilterNil);
            let c2 = Circuit::new(arenas2, true, DecomposeGadgets::new(FilterNil, |_| true));

            let gk1 = c1.intern_gadget_kind(WideMul2);
            let gk2 = c2.intern_gadget_kind(WideMul2);

            for a_val in 0 .. 16 {
                let a1 = c1.lit(c1.ty(a_ty), a_val);
                let a2 = c2.lit(c2.ty(a_ty), a_val);
                for b_val in 0 .. 16 {
                    let b1 = c1.lit(c1.ty(b_ty), b_val);
                    let b2 = c2.lit(c2.ty(b_ty), b_val);

                    let out1 = c1.gadget(gk1, &[a1, b1]);
                    let out2 = c2.gadget(gk2, &[a2, b2]);

                    let out1_val = eval::eval_wire_public(&c1, out1);
                    let out2_val = eval::eval_wire_public(&c2, out2);
                    assert_eq!(out1_val, out2_val, "on inputs {}, {}", a_val, b_val);
                }
            }
        }

        let arenas = Arenas::new();
        inner(&arenas, &arenas, a_ty, b_ty);
    }

    #[test]
    fn wide_mul2_unsigned() {
        wide_mul2_common(TyKind::Uint(IntSize(4)), TyKind::Uint(IntSize(4)));
    }

    #[test]
    fn wide_mul2_signed() {
        wide_mul2_common(TyKind::Int(IntSize(4)), TyKind::Int(IntSize(4)));
    }

    #[test]
    fn wide_mul2_mixed() {
        wide_mul2_common(TyKind::Int(IntSize(4)), TyKind::Uint(IntSize(4)));
        wide_mul2_common(TyKind::Uint(IntSize(4)), TyKind::Int(IntSize(4)));
    }


    #[test]
    fn wide_mul2_odd() {
        wide_mul2_common(TyKind::Uint(IntSize(3)), TyKind::Uint(IntSize(3)));
        wide_mul2_common(TyKind::Int(IntSize(3)), TyKind::Int(IntSize(3)));
        wide_mul2_common(TyKind::Int(IntSize(3)), TyKind::Uint(IntSize(3)));
        wide_mul2_common(TyKind::Uint(IntSize(3)), TyKind::Int(IntSize(3)));
    }
}
