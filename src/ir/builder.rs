use std::mem::MaybeUninit;
use bumpalo::Bump;
use crate::ir::circuit::{Circuit, Wire, Ty, TyKind, UnOp, BinOp, ShiftOp, CmpOp};

pub struct Builder<'a> {
    c: Circuit<'a>,
}

impl<'a> Builder<'a> {
    pub fn new(arena: &'a Bump, input_tys: Vec<TyKind>) -> Builder<'a> {
        Builder { c: Circuit::new(arena, input_tys) }
    }

    pub fn circuit(&self) -> &Circuit<'a> {
        &self.c
    }
}

macro_rules! define_un_ops {
    (
        $( $Op:ident :: $op:ident; )*
    ) => {
        $(
            pub trait $Op<'a> {
                type Output;
                fn $op(bld: &Builder<'a>, a: Self) -> Self::Output;
            }

            impl<'a> $Op<'a> for Wire<'a> {
                type Output = Wire<'a>;
                fn $op(bld: &Builder<'a>, a: Wire<'a>) -> Wire<'a> {
                    bld.c.unary(UnOp::$Op, a)
                }
            }
        )*

        impl<'a> Builder<'a> {
            $(
                pub fn $op<A: $Op<'a>>(&self, a: A) -> A::Output {
                    $Op::$op(self, a)
                }
            )*
        }
    };
}

define_un_ops! {
    Neg::neg;
    Not::not;
}

macro_rules! define_bin_ops {
    (
        $( $Op:ident :: $op:ident; )*
    ) => {
        $(
            pub trait $Op<'a, Other = Self> {
                type Output;
                fn $op(bld: &Builder<'a>, a: Self, b: Other) -> Self::Output;
            }

            impl<'a> $Op<'a> for Wire<'a> {
                type Output = Wire<'a>;
                fn $op(bld: &Builder<'a>, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
                    bld.c.binary(BinOp::$Op, a, b)
                }
            }
        )*

        impl<'a> Builder<'a> {
            $(
                pub fn $op<A: $Op<'a, B>, B>(&self, a: A, b: B) -> A::Output {
                    $Op::$op(self, a, b)
                }
            )*
        }
    };
}

define_bin_ops! {
    Add::add;
    Sub::sub;
    Mul::mul;
    Div::div;
    Mod::mod_;
    And::and;
    Or::or;
    Xor::xor;
}

macro_rules! define_shift_ops {
    (
        $( $Op:ident :: $op:ident; )*
    ) => {
        $(
            pub trait $Op<'a, Other> {
                type Output;
                fn $op(bld: &Builder<'a>, a: Self, b: Other) -> Self::Output;
            }

            impl<'a> $Op<'a, u8> for Wire<'a> {
                type Output = Wire<'a>;
                fn $op(bld: &Builder<'a>, a: Wire<'a>, b: u8) -> Wire<'a> {
                    let b = bld.c.lit(Ty::new(TyKind::U8), b as u64);
                    bld.c.shift(ShiftOp::$Op, a, b)
                }
            }

            impl<'a> $Op<'a, Wire<'a>> for Wire<'a> {
                type Output = Wire<'a>;
                fn $op(bld: &Builder<'a>, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
                    bld.c.shift(ShiftOp::$Op, a, b)
                }
            }
        )*

        impl<'a> Builder<'a> {
            $(
                pub fn $op<A: $Op<'a, B>, B>(&self, a: A, b: B) -> A::Output {
                    $Op::$op(self, a, b)
                }
            )*
        }
    };
}

define_shift_ops! {
    Shl::shl;
    Shr::shr;
}

macro_rules! define_cmp_ops {
    (
        $( $Op:ident :: $op:ident; )*
    ) => {
        $(
            pub trait $Op<'a, Other = Self> {
                type Output;
                fn $op(bld: &Builder<'a>, a: Self, b: Other) -> Self::Output;
            }

            impl<'a> $Op<'a> for Wire<'a> {
                type Output = Wire<'a>;
                fn $op(bld: &Builder<'a>, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
                    bld.c.compare(CmpOp::$Op, a, b)
                }
            }
        )*

        impl<'a> Builder<'a> {
            $(
                pub fn $op<A: $Op<'a, B>, B>(&self, a: A, b: B) -> A::Output {
                    $Op::$op(self, a, b)
                }
            )*
        }
    };
}

define_cmp_ops! {
    Eq::eq;
    Ne::ne;
    Lt::lt;
    Le::le;
    Gt::gt;
    Ge::ge;
}

pub trait Mux<'a, Cond, Other = Self> {
    type Output;
    fn mux(bld: &Builder<'a>, c: Cond, t: Self, e: Other) -> Self::Output;
}

impl<'a> Mux<'a, Wire<'a>> for Wire<'a> {
    type Output = Wire<'a>;
    fn mux(bld: &Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        bld.c.mux(c, t, e)
    }
}

impl<'a> Builder<'a> {
    pub fn mux<T: Mux<'a, C, E>, C, E>(&self, c: C, t: T, e: E) -> T::Output {
        Mux::mux(self, c, t, e)
    }
}

macro_rules! mux_tuple_impl {
    ($($A:ident $B:ident),*) => {
        impl<'a, $($A: Mux<'a, C, $B>, $B,)* C: Copy> Mux<'a, C, ($($B,)*)> for ($($A,)*) {
            type Output = ($(<$A as Mux<'a, C, $B>>::Output,)*);

            fn mux(bld: &Builder<'a>, c: C, a: ($($A,)*), b: ($($B,)*)) -> Self::Output {
                #![allow(bad_style)]    // Capitalized variable names $A, $B
                #![allow(unused)]       // `bld` in the zero-element case
                let ($($A,)*) = a;
                let ($($B,)*) = b;
                ($(<$A as Mux<C, $B>>::mux(bld, c, $A, $B),)*)
            }
        }
    };
}

mux_tuple_impl!();
mux_tuple_impl!(A1 B1);
mux_tuple_impl!(A1 B1, A2 B2);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8, A9 B9);
mux_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8, A9 B9, A10 B10);

macro_rules! mux_array_impls {
    ($($n:expr),*) => {
        $(
            impl<'a, A: Mux<'a, C, B>, B, C: Copy> Mux<'a, C, [B; $n]> for [A; $n] {
                type Output = [<A as Mux<'a, C, B>>::Output; $n];

                fn mux(bld: &Builder<'a>, c: C, a: [A; $n], b: [B; $n]) -> Self::Output {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let a = MaybeUninit::new(a);
                        let b = MaybeUninit::new(b);
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let a_val = (a.as_ptr() as *const A).add(i).read();
                            let b_val = (b.as_ptr() as *const B).add(i).read();
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = Mux::mux(bld, c, a_val, b_val);

                            (o.as_mut_ptr() as *mut A::Output).add(i).write(o_val);
                        }

                        o.assume_init()
                    }
                }
            }
        )*
    };
}

mux_array_impls!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32
);

impl<'a, A: Mux<'a, C, B>, B, C: Copy> Mux<'a, C, Vec<B>> for Vec<A> {
    type Output = Vec<<A as Mux<'a, C, B>>::Output>;

    fn mux(bld: &Builder<'a>, c: C, a: Vec<A>, b: Vec<B>) -> Self::Output {
        assert!(
            a.len() == b.len(),
            "can't mux Vecs with different len ({} != {})", a.len(), b.len(),
        );
        a.into_iter().zip(b.into_iter()).map(|(a_val, b_val)| {
            Mux::mux(bld, c, a_val, b_val)
        }).collect::<Vec<_>>()
    }
}
