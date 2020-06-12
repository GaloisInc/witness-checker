use std::marker::PhantomData;
use std::mem::MaybeUninit;
use crate::ir::builder::{self, Builder};
use crate::ir::circuit::{Wire, Ty, TyKind};


pub trait Repr<'a> {
    type Repr;

    fn lit(bld: &Builder<'a>, x: Self) -> Self::Repr;
}

macro_rules! repr_tuple_impl {
    ($($A:ident $B:ident),*) => {
        impl<'a, $($A: Repr<'a>,)*> Repr<'a> for ($($A,)*) {
            type Repr = ($(<$A as Repr<'a>>::Repr,)*);

            fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                let ($($A,)*) = a;
                ($($A::lit(bld, $A),)*)
            }
        }
    };
}

repr_tuple_impl!();
repr_tuple_impl!(A1 B1);
repr_tuple_impl!(A1 B1, A2 B2);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8, A9 B9);
repr_tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8, A9 B9, A10 B10);

macro_rules! repr_array_impls {
    ($($n:expr),*) => {
        $(
            impl<'a, A: Repr<'a>> Repr<'a> for [A; $n] {
                type Repr = [A::Repr; $n];

                fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let a = MaybeUninit::new(a);
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let a_val = (a.as_ptr() as *const A).add(i).read();
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = Repr::lit(bld, a_val);

                            (o.as_mut_ptr() as *mut A::Repr).add(i).write(o_val);
                        }

                        o.assume_init()
                    }
                }
            }
        )*
    };
}

repr_array_impls!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32
);

impl<'a, A: Repr<'a>> Repr<'a> for Vec<A> {
    type Repr = Vec<A::Repr>;

    fn lit(bld: &Builder<'a>, a: Self) -> Self::Repr {
        a.into_iter().map(|a_val| A::lit(bld, a_val)).collect::<Vec<_>>()
    }
}


pub struct TWire<'a, T: Repr<'a>> {
    repr: T::Repr,
}

impl<'a, T: Repr<'a>> TWire<'a, T> {
    pub fn new(repr: T::Repr) -> TWire<'a, T> {
        TWire {
            repr,
        }
    }
}

type ReprOf<'a, T> = <T as Repr<'a>>::Repr;



macro_rules! define_unary_op {
    ($Op:ident :: $op:ident) => {
        /// Marker trait for Rust types on which this circuit operation makes sense.  The
        /// underlying circuit-level representations for these types must support the circuit-level
        /// operation (as expressed by the `ReprOf<Self>: builder::$Op<...>` constraint).  This
        /// marker trait exists because not all Rust types with appropriate `Repr`s should support
        /// the operation.  For example, we don't want to allow adding a `u16` to a `u8`, even
        /// though both `u16::Repr` and `u8::Repr` are `Wire`, which supports `builder::Add`.
        pub trait $Op<'a>
        where
            Self: Repr<'a>,
            ReprOf<'a, Self>: builder::$Op<'a, Output = ReprOf<'a, Self::Output>>,
        {
            type Output: Repr<'a>;
        }

        impl<'a, X> builder::$Op<'a> for TWire<'a, X>
        where
            X: Repr<'a> + $Op<'a>,
            ReprOf<'a, X>: builder::$Op<
                'a,
                Output = ReprOf<'a, <X as $Op<'a>>::Output>,
            >,
        {
            type Output = TWire<'a, <X as $Op<'a>>::Output>;

            fn $op(
                bld: &Builder<'a>,
                x: TWire<'a, X>,
            ) -> TWire<'a, <X as $Op<'a>>::Output> {
                TWire::new(builder::$Op::$op(bld, x.repr))
            }
        }
    };
}

macro_rules! define_binary_op {
    ($Op:ident :: $op:ident) => {
        /// Marker trait for Rust types on which this circuit operation makes sense.  The
        /// underlying circuit-level representations for these types must support the circuit-level
        /// operation (as expressed by the `ReprOf<Self>: builder::$Op<...>` constraint).  This
        /// marker trait exists because not all Rust types with appropriate `Repr`s should support
        /// the operation.  For example, we don't want to allow adding a `u16` to a `u8`, even
        /// though both `u16::Repr` and `u8::Repr` are `Wire`, which supports `builder::Add`.
        pub trait $Op<'a, Other = Self>
        where
            Self: Repr<'a>,
            Other: Repr<'a>,
            ReprOf<'a, Self>: builder::$Op<'a, ReprOf<'a, Other>, Output = ReprOf<'a, Self::Output>>,
        {
            type Output: Repr<'a>;
        }

        impl<'a, X, Y> builder::$Op<
            'a,
            TWire<'a, Y>,
        > for TWire<'a, X>
        where
            X: Repr<'a> + $Op<'a, Y>,
            Y: Repr<'a>,
            ReprOf<'a, X>: builder::$Op<
                'a,
                ReprOf<'a, Y>,
                Output = ReprOf<'a, <X as $Op<'a, Y>>::Output>,
            >,
        {
            type Output = TWire<'a, <X as $Op<'a, Y>>::Output>;

            fn $op(
                bld: &Builder<'a>,
                x: TWire<'a, X>,
                y: TWire<'a, Y>,
            ) -> TWire<'a, <X as $Op<'a, Y>>::Output> {
                TWire::new(builder::$Op::$op(bld, x.repr, y.repr))
            }
        }
    };
}

macro_rules! define_mux {
    ($Op:ident :: $op:ident) => {
        /// Marker trait for Rust types on which this circuit operation makes sense.  The
        /// underlying circuit-level representations for these types must support the circuit-level
        /// operation (as expressed by the `ReprOf<Self>: builder::$Op<...>` constraint).  This
        /// marker trait exists because not all Rust types with appropriate `Repr`s should support
        /// the operation.  For example, we don't want to allow adding a `u16` to a `u8`, even
        /// though both `u16::Repr` and `u8::Repr` are `Wire`, which supports `builder::Add`.
        pub trait $Op<'a, Cond, Other = Self>
        where
            Cond: Repr<'a>,
            Self: Repr<'a>,
            Other: Repr<'a>,
            ReprOf<'a, Self>: builder::$Op<
                'a,
                ReprOf<'a, Cond>,
                ReprOf<'a, Other>,
                Output = ReprOf<'a, Self::Output>,
            >,
        {
            type Output: Repr<'a>;
        }

        impl<'a, C, T, E> builder::$Op<
            'a,
            TWire<'a, C>,
            TWire<'a, E>,
        > for TWire<'a, T>
        where
            C: Repr<'a>,
            T: Repr<'a> + $Op<'a, C, E>,
            E: Repr<'a>,
            ReprOf<'a, T>: builder::$Op<
                'a,
                ReprOf<'a, C>,
                ReprOf<'a, E>,
                Output = ReprOf<'a, <T as $Op<'a, C, E>>::Output>,
            >,
        {
            type Output = TWire<'a, <T as $Op<'a, C, E>>::Output>;

            fn $op(
                bld: &Builder<'a>,
                c: TWire<'a, C>,
                t: TWire<'a, T>,
                e: TWire<'a, E>,
            ) -> TWire<'a, <T as $Op<'a, C, E>>::Output> {
                TWire::new(builder::$Op::$op(bld, c.repr, t.repr, e.repr))
            }
        }
    };
}

define_unary_op!(Neg::neg);
define_unary_op!(Not::not);
define_binary_op!(Add::add);
define_binary_op!(Sub::sub);
define_binary_op!(Mul::mul);
define_binary_op!(Div::div);
define_binary_op!(Mod::mod_);
define_binary_op!(And::and);
define_binary_op!(Or::or);
define_binary_op!(Xor::xor);
define_binary_op!(Shl::shl);
define_binary_op!(Shr::shr);
define_binary_op!(Eq::eq);
define_binary_op!(Ne::ne);
define_binary_op!(Lt::lt);
define_binary_op!(Le::le);
define_binary_op!(Gt::gt);
define_binary_op!(Ge::ge);
define_mux!(Mux::mux);


macro_rules! define_prim_reprs {
    ($($T:ty = $TyKind:ident,)*) => {
        $(
            impl<'a> Repr<'a> for $T {
                type Repr = Wire<'a>;
                fn lit(bld: &Builder<'a>, x: $T) -> Wire<'a> {
                    bld.circuit().lit(Ty::new(TyKind::$TyKind), x as u64)
                }
            }

            impl<'a> Neg<'a> for $T { type Output = $T; }
            impl<'a> Not<'a> for $T { type Output = $T; }
            impl<'a> Add<'a> for $T { type Output = $T; }
            impl<'a> Sub<'a> for $T { type Output = $T; }
            impl<'a> Mul<'a> for $T { type Output = $T; }
            impl<'a> Div<'a> for $T { type Output = $T; }
            impl<'a> Mod<'a> for $T { type Output = $T; }
            impl<'a> And<'a> for $T { type Output = $T; }
            impl<'a> Or<'a> for $T { type Output = $T; }
            impl<'a> Xor<'a> for $T { type Output = $T; }
            impl<'a> Shl<'a, u8> for $T { type Output = $T; }
            impl<'a> Shr<'a, u8> for $T { type Output = $T; }
            impl<'a> Eq<'a> for $T { type Output = bool; }
            impl<'a> Ne<'a> for $T { type Output = bool; }
            impl<'a> Lt<'a> for $T { type Output = bool; }
            impl<'a> Le<'a> for $T { type Output = bool; }
            impl<'a> Gt<'a> for $T { type Output = bool; }
            impl<'a> Ge<'a> for $T { type Output = bool; }
            impl<'a> Mux<'a, bool> for $T { type Output = $T; }
        )*
    };
}

define_prim_reprs! {
    bool = Bool,
    i8 = I8,
    i16 = I16,
    i32 = I32,
    i64 = I64,
    u8 = U8,
    u16 = U16,
    u32 = U32,
    u64 = U64,
}


macro_rules! mux_tuple_impl {
    ($($A:ident $B:ident),*) => {
        impl<'a, $($A: Mux<'a, C, $B>, $B,)* C> Mux<'a, C, ($($B,)*)> for ($($A,)*)
        where
            $($A: Repr<'a>,)*
            $($B: Repr<'a>,)*
            C: Repr<'a>,
            C::Repr: Copy,
            $(ReprOf<'a, $A>: builder::Mux<
                'a,
                ReprOf<'a, C>,
                ReprOf<'a, $B>,
                Output = ReprOf<'a, $A::Output>,
            >,)*
        {
            type Output = ($(<$A as Mux<'a, C, $B>>::Output,)*);
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
            impl<'a, A: Mux<'a, C, B>, B, C> Mux<'a, C, [B; $n]> for [A; $n]
            where
                A: Repr<'a>,
                B: Repr<'a>,
                C: Repr<'a>,
                C::Repr: Copy,
                ReprOf<'a, A>: builder::Mux<
                    'a,
                    ReprOf<'a, C>,
                    ReprOf<'a, B>,
                    Output = ReprOf<'a, A::Output>,
                >,
            {
                type Output = [<A as Mux<'a, C, B>>::Output; $n];
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

impl<'a, A: Mux<'a, C, B>, B, C> Mux<'a, C, Vec<B>> for Vec<A>
where
    A: Repr<'a>,
    B: Repr<'a>,
    C: Repr<'a>,
    C::Repr: Copy,
    ReprOf<'a, A>: builder::Mux<
        'a,
        ReprOf<'a, C>,
        ReprOf<'a, B>,
        Output = ReprOf<'a, A::Output>,
    >,
{
    type Output = Vec<<A as Mux<'a, C, B>>::Output>;
}
