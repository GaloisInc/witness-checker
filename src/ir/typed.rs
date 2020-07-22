use std::mem::MaybeUninit;
use std::ops::Deref;
use bumpalo::Bump;
use crate::ir::circuit::{Circuit, Wire, TyKind};


pub struct Builder<'a> {
    c: Circuit<'a>,
}

impl<'a> Builder<'a> {
    pub fn new(arena: &'a Bump) -> Builder<'a> {
        Builder { c: Circuit::new(arena) }
    }

    pub fn circuit(&self) -> &Circuit<'a> {
        &self.c
    }

    pub fn finish(self) -> Circuit<'a> {
        self.c
    }
}

pub trait AsBuilder<'a> {
    fn as_builder(&self) -> &Builder<'a>;
}

impl<'a> AsBuilder<'a> for Builder<'a> {
    fn as_builder(&self) -> &Builder<'a> { self }
}

/// Typed wire, which carries a a representation of `T`.  This is useful for distinguishing wires
/// with different high-level types, even when they share a low-level representation.
pub struct TWire<'a, T: Repr<'a>> {
    pub repr: T::Repr,
}

impl<'a, T: Repr<'a>> TWire<'a, T> {
    pub fn new(repr: T::Repr) -> TWire<'a, T> {
        TWire {
            repr,
        }
    }
}

impl<'a, T> Clone for TWire<'a, T>
where T: Repr<'a>, T::Repr: Clone {
    fn clone(&self) -> Self {
        TWire {
            repr: self.repr.clone(),
        }
    }
}

impl<'a, T> Copy for TWire<'a, T>
where T: Repr<'a>, T::Repr: Copy {
}

impl<'a, T: Repr<'a>> Deref for TWire<'a, T> {
    type Target = T::Repr;
    fn deref(&self) -> &T::Repr {
        &self.repr
    }
}



pub trait Repr<'a> {
    type Repr;
}


pub trait Lit<'a>
where Self: Repr<'a> {
    fn lit(bld: &Builder<'a>, x: Self) -> Self::Repr;
}

pub trait Secret<'a>
where Self: Repr<'a> + Sized {
    fn secret(bld: &Builder<'a>, x: Option<Self>) -> Self::Repr;
}

impl<'a> Builder<'a> {
    pub fn lit<T: Lit<'a>>(&self, x: T) -> TWire<'a, T> {
        TWire::new(Lit::lit(self, x))
    }

    pub fn secret<T: Secret<'a>>(&self, x: Option<T>) -> TWire<'a, T> {
        TWire::new(Secret::secret(self, x))
    }
}


macro_rules! define_un_ops {
    (
        $( $Op:ident :: $op:ident; )*
    ) => {
        $(
            pub trait $Op<'a>: Repr<'a> {
                type Output: Repr<'a>;
                fn $op(bld: &Builder<'a>, a: Self::Repr) -> <Self::Output as Repr<'a>>::Repr;
            }
        )*

        impl<'a> Builder<'a> {
            $(
                pub fn $op<A: $Op<'a>>(&self, a: TWire<'a, A>) -> TWire<'a, A::Output> {
                    TWire::new(<A as $Op>::$op(self, a.repr))
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
            pub trait $Op<'a, Other = Self>
            where Self: Repr<'a>, Other: Repr<'a> {
                type Output: Repr<'a>;
                fn $op(
                    bld: &Builder<'a>,
                    a: Self::Repr,
                    b: Other::Repr,
                ) -> <Self::Output as Repr<'a>>::Repr;
            }
        )*

        impl<'a> Builder<'a> {
            $(
                pub fn $op<A: $Op<'a, B>, B: Repr<'a>>(
                    &self,
                    a: TWire<'a, A>,
                    b: TWire<'a, B>,
                ) -> TWire<'a, A::Output> {
                    TWire::new(<A as $Op<B>>::$op(self, a.repr, b.repr))
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
    Shl::shl;
    Shr::shr;
    Eq::eq;
    Ne::ne;
    Lt::lt;
    Le::le;
    Gt::gt;
    Ge::ge;
}

pub trait Mux<'a, Cond, Other = Self>
where Cond: Repr<'a>, Self: Repr<'a>, Other: Repr<'a> {
    type Output: Repr<'a>;
    fn mux(
        bld: &Builder<'a>,
        c: Cond::Repr,
        t: Self::Repr,
        e: Other::Repr,
    ) -> <Self::Output as Repr<'a>>::Repr;
}

impl<'a> Builder<'a> {
    pub fn mux<C: Repr<'a>, T: Mux<'a, C, E>, E: Repr<'a>>(
        &self,
        c: TWire<'a, C>,
        t: TWire<'a, T>,
        e: TWire<'a, E>,
    ) -> TWire<'a, T::Output> {
        TWire::new(<T as Mux<C, E>>::mux(self, c.repr, t.repr, e.repr))
    }
}


macro_rules! primitive_unary_impl {
    ($Op:ident :: $op:ident ($T:ty)) => {
        impl<'a> $Op<'a> for $T {
            type Output = $T;
            fn $op(bld: &Builder<'a>, a: Wire<'a>) -> Wire<'a> {
                bld.c.$op(a)
            }
        }
    };
}

macro_rules! primitive_binary_impl {
    ($Op:ident :: $op:ident ($T:ty, $U:ty) -> $R:ty) => {
        impl<'a> $Op<'a, $U> for $T {
            type Output = $R;
            fn $op(bld: &Builder<'a>, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
                bld.c.$op(a, b)
            }
        }
    };
}

impl<'a> Repr<'a> for bool {
    type Repr = Wire<'a>;
}

impl<'a> Lit<'a> for bool {
    fn lit(bld: &Builder<'a>, x: bool) -> Wire<'a> {
        bld.c.lit(bld.c.ty(TyKind::Bool), x as u64)
    }
}

impl<'a> Secret<'a> for bool {
    fn secret(bld: &Builder<'a>, x: Option<bool>) -> Wire<'a> {
        bld.c.new_secret(bld.c.ty(TyKind::Bool), x.map(|x| x as u64))
    }
}

primitive_unary_impl!(Not::not(bool));
primitive_binary_impl!(And::and(bool, bool) -> bool);
primitive_binary_impl!(Or::or(bool, bool) -> bool);
primitive_binary_impl!(Xor::xor(bool, bool) -> bool);
primitive_binary_impl!(Eq::eq(bool, bool) -> bool);
primitive_binary_impl!(Ne::ne(bool, bool) -> bool);
primitive_binary_impl!(Lt::lt(bool, bool) -> bool);
primitive_binary_impl!(Le::le(bool, bool) -> bool);
primitive_binary_impl!(Gt::gt(bool, bool) -> bool);
primitive_binary_impl!(Ge::ge(bool, bool) -> bool);

impl<'a> Mux<'a, bool> for bool {
    type Output = bool;
    fn mux(bld: &Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        bld.c.mux(c, t, e)
    }
}

macro_rules! integer_impls {
    ($T:ty, $K:ident) => {
        impl<'a> Repr<'a> for $T {
            type Repr = Wire<'a>;
        }

        impl<'a> Lit<'a> for $T {
            fn lit(bld: &Builder<'a>, x: $T) -> Wire<'a> {
                bld.c.lit(bld.c.ty(TyKind::$K), x as u64)
            }
        }

        impl<'a> Secret<'a> for $T {
            fn secret(bld: &Builder<'a>, x: Option<$T>) -> Wire<'a> {
                bld.c.new_secret(bld.c.ty(TyKind::$K), x.map(|x| x as u64))
            }
        }

        primitive_unary_impl!(Neg::neg($T));
        primitive_unary_impl!(Not::not($T));
        primitive_binary_impl!(Add::add($T, $T) -> $T);
        primitive_binary_impl!(Sub::sub($T, $T) -> $T);
        primitive_binary_impl!(Mul::mul($T, $T) -> $T);
        primitive_binary_impl!(Div::div($T, $T) -> $T);
        primitive_binary_impl!(Mod::mod_($T, $T) -> $T);
        primitive_binary_impl!(And::and($T, $T) -> $T);
        primitive_binary_impl!(Or::or($T, $T) -> $T);
        primitive_binary_impl!(Xor::xor($T, $T) -> $T);
        primitive_binary_impl!(Shl::shl($T, u8) -> $T);
        primitive_binary_impl!(Shr::shr($T, u8) -> $T);
        primitive_binary_impl!(Eq::eq($T, $T) -> bool);
        primitive_binary_impl!(Ne::ne($T, $T) -> bool);
        primitive_binary_impl!(Lt::lt($T, $T) -> bool);
        primitive_binary_impl!(Le::le($T, $T) -> bool);
        primitive_binary_impl!(Gt::gt($T, $T) -> bool);
        primitive_binary_impl!(Ge::ge($T, $T) -> bool);

        impl<'a> Mux<'a, bool> for $T {
            type Output = $T;
            fn mux(bld: &Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
                bld.c.mux(c, t, e)
            }
        }

    };
}

integer_impls!(i8, I8);
integer_impls!(i16, I16);
integer_impls!(i32, I32);
integer_impls!(i64, I64);
integer_impls!(u8, U8);
integer_impls!(u16, U16);
integer_impls!(u32, U32);
integer_impls!(u64, U64);


macro_rules! tuple_impl {
    ($($A:ident $B:ident),*) => {
        impl<'a, $($A: Repr<'a>,)*> Repr<'a> for ($($A,)*) {
            type Repr = ($(TWire<'a, $A>,)*);
        }

        impl<'a, $($A: Lit<'a>,)*> Lit<'a> for ($($A,)*) {
            fn lit(bld: &Builder<'a>, x: Self) -> Self::Repr {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                let ($($A,)*) = x;
                ($(bld.lit($A),)*)
            }
        }

        impl<'a, $($A: Secret<'a>,)*> Secret<'a> for ($($A,)*) {
            fn secret(bld: &Builder<'a>, x: Option<Self>) -> Self::Repr {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                if let Some(($($A,)*)) = x {
                    ($(bld.secret(Some($A)),)*)
                } else {
                    ($(bld.secret::<$A>(None),)*)
                }
            }
        }

        impl<'a, C, $($A,)* $($B,)*> Mux<'a, C, ($($B,)*)> for ($($A,)*)
        where
            C: Repr<'a>,
            C::Repr: Clone,
            $($A: Repr<'a> + Mux<'a, C, $B>,)*
            $($B: Repr<'a>,)*
        {
            type Output = ($(<$A as Mux<'a, C, $B>>::Output,)*);

            fn mux(
                bld: &Builder<'a>,
                c: C::Repr,
                a: ($(TWire<'a, $A>,)*),
                b: ($(TWire<'a, $B>,)*),
            ) -> ($(TWire<'a, <$A as Mux<'a, C, $B>>::Output>,)*) {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                let ($($A,)*) = a;
                let ($($B,)*) = b;
                let c = TWire::<C>::new(c);
                ($(bld.mux(c.clone(), $A, $B),)*)
            }
        }
    };
}

tuple_impl!();
tuple_impl!(A1 B1);
tuple_impl!(A1 B1, A2 B2);
tuple_impl!(A1 B1, A2 B2, A3 B3);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8, A9 B9);
tuple_impl!(A1 B1, A2 B2, A3 B3, A4 B4, A5 B5, A6 B6, A7 B7, A8 B8, A9 B9, A10 B10);


macro_rules! array_impls {
    ($($n:expr),*) => {
        $(
            impl<'a, A: Repr<'a>> Repr<'a> for [A; $n] {
                type Repr = [TWire<'a, A>; $n];
            }

            impl<'a, A: Lit<'a>> Lit<'a> for [A; $n] {
                fn lit(bld: &Builder<'a>, a: [A; $n]) -> [TWire<'a, A>; $n] {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let a = MaybeUninit::new(a);
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let a_val = (a.as_ptr() as *const A).add(i).read();
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = bld.lit(a_val);

                            (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                        }

                        o.assume_init()
                    }
                }
            }

            impl<'a, A: Secret<'a>> Secret<'a> for [A; $n] {
                fn secret(bld: &Builder<'a>, a: Option<[A; $n]>) -> [TWire<'a, A>; $n] {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let mut o = MaybeUninit::uninit();

                        if let Some(a) = a {
                            let a = MaybeUninit::new(a);
                            for i in 0 .. $n {
                                let a_val = (a.as_ptr() as *const A).add(i).read();
                                // If this panics, the remaining elements of `a` and `b` will leak.
                                let o_val = bld.secret(Some(a_val));
                                (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                            }
                        } else {
                            for i in 0 .. $n {
                                let o_val = bld.secret::<A>(None);
                                (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                            }
                        }

                        o.assume_init()
                    }
                }
            }

            impl<'a, C, A, B> Mux<'a, C, [B; $n]> for [A; $n]
            where
                C: Repr<'a>,
                C::Repr: Clone,
                A: Repr<'a> + Mux<'a, C, B>,
                B: Repr<'a>,
            {
                type Output = [<A as Mux<'a, C, B>>::Output; $n];

                fn mux(
                    bld: &Builder<'a>,
                    c: C::Repr,
                    a: [TWire<'a, A>; $n],
                    b: [TWire<'a, B>; $n],
                ) -> [TWire<'a, A::Output>; $n] {
                    let c = TWire::<C>::new(c);

                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let a = MaybeUninit::new(a);
                        let b = MaybeUninit::new(b);
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let a_val = (a.as_ptr() as *const TWire<A>).add(i).read();
                            let b_val = (b.as_ptr() as *const TWire<B>).add(i).read();
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = bld.mux(c.clone(), a_val, b_val);

                            (o.as_mut_ptr() as *mut TWire<A::Output>)
                                .add(i).write(o_val);
                        }

                        o.assume_init()
                    }
                }
            }
        )*
    };
}

array_impls!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32
);


impl<'a, A: Repr<'a>> Repr<'a> for Vec<A> {
    type Repr = Vec<TWire<'a, A>>;
}

impl<'a, A: Lit<'a>> Lit<'a> for Vec<A> {
    fn lit(bld: &Builder<'a>, a: Vec<A>) -> Vec<TWire<'a, A>> {
        a.into_iter().map(|x| bld.lit(x)).collect()
    }
}

// No `impl Secret for Vec<A>`, since we can't determine how many wires to create in the case where
// the value is unknown.

impl<'a, C, A, B> Mux<'a, C, Vec<B>> for Vec<A>
where
    C: Repr<'a>,
    C::Repr: Clone,
    A: Repr<'a> + Mux<'a, C, B>,
    B: Repr<'a>,
{
    type Output = Vec<A::Output>;

    fn mux(
        bld: &Builder<'a>,
        c: C::Repr,
        a: Vec<TWire<'a, A>>,
        b: Vec<TWire<'a, B>>,
    ) -> Vec<TWire<'a, A::Output>> {
        assert!(
            a.len() == b.len(),
            "can't mux Vecs of unequal len ({} != {})", a.len(), b.len(),
        );
        let c = TWire::<C>::new(c);
        a.into_iter().zip(b.into_iter()).map(|(a, b)| bld.mux(c.clone(), a, b)).collect()
    }
}


impl<'a> Builder<'a> {
    pub fn mux_multi<C, A>(
        &self,
        cases: &[TWire<'a, (C, A)>],
        default: TWire<'a, A>,
    ) -> TWire<'a, A>
    where
        C: Repr<'a>,
        A: Mux<'a, C, A, Output = A>,
        C::Repr: Clone,
        A::Repr: Clone,
    {
        let mut val = default;
        for case in cases {
            let (cond, then) = case.clone().repr;
            val = self.mux(cond, then, val);
        }
        val
    }

    pub fn index<I, T>(
        &self,
        arr: &[TWire<'a, T>],
        idx: TWire<'a, I>,
        mut mk_idx: impl FnMut(&Self, usize) -> TWire<'a, I>,
    ) -> TWire<'a, T>
    where
        I: Eq<'a, I>,
        I::Repr: Clone,
        T: Mux<'a, <I as Eq<'a, I>>::Output, T, Output = T>,
        T::Repr: Clone,
    {
        let mut val = arr.first().expect("can't index in an empty array").clone();
        for (i, x) in arr.iter().enumerate().skip(1) {
            let eq = self.eq(idx.clone(), mk_idx(self, i));
            val = self.mux(eq, x.clone(), val);
        }
        val
    }
}
