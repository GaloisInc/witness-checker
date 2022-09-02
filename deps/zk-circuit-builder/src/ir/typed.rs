use std::cmp;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::MaybeUninit;
use std::ops::{Deref, DerefMut};
use std::ptr;
use generic_array::{ArrayLength, GenericArray};
use generic_array::typenum::{Sum, Quot, U3, U4};
use num_traits::Zero;
use scuttlebutt::field::{FiniteField, Gf40, Gf45, F56b, F63b, F64b};
use crate::eval::Evaluator;
use crate::ir::circuit::{AsBits, Bits, CircuitBase, CircuitTrait, CircuitExt, DynCircuit, Field, FromBits, IntSize, Wire, Ty, TyKind, CellResetGuard};
use crate::ir::migrate::{self, Migrate};

pub struct Builder<'a> {
    c: &'a DynCircuit<'a>,
}

impl<'a> Builder<'a> {
    pub fn new(c: &'a DynCircuit<'a>) -> Builder<'a> {
        Builder { c: c }
    }

    pub fn is_prover(&self) -> bool {
        self.c.is_prover()
    }

    pub fn circuit(&self) -> &'a DynCircuit<'a> {
        &self.c
    }

    pub fn scoped_label<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        self.c.scoped_label(label)
    }

    pub fn with_label<T: fmt::Display, F: FnOnce() -> R, R>(&self, label: T, f: F) -> R {
        self.c.with_label(label, f)
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
#[derive(Debug)]
pub struct TWire<'a, T: Repr<'a> + ?Sized> {
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

impl<'a, T, U> PartialEq<TWire<'a, U>> for TWire<'a, T>
where T: Repr<'a>, U: Repr<'a>, T::Repr: PartialEq<U::Repr> {
    fn eq(&self, other: &TWire<'a, U>) -> bool {
        self.repr.eq(&other.repr)
    }

    fn ne(&self, other: &TWire<'a, U>) -> bool {
        self.repr.ne(&other.repr)
    }
}

impl<'a, T> cmp::Eq for TWire<'a, T>
where T: Repr<'a>, T::Repr: cmp::Eq {
}

impl<'a, T> Hash for TWire<'a, T>
where T: Repr<'a>, T::Repr: Hash {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.repr.hash(state)
    }
}

impl<'a, T: Repr<'a>> Deref for TWire<'a, T> {
    type Target = T::Repr;
    fn deref(&self) -> &T::Repr {
        &self.repr
    }
}

impl<'a, T: Repr<'a>> DerefMut for TWire<'a, T> {
    fn deref_mut(&mut self) -> &mut T::Repr {
        &mut self.repr
    }
}


/// Typed analogue to `circuit::SecretHandle`.  Call `set()` to initialize the secret value, or
/// drop it to apply the default, if one was provided at construction time.
pub struct TSecretHandle<'a, T: Repr<'a> + Secret<'a> + ?Sized> {
    /// `TSecretHandle` doesn't actually store any `SecretHandle`s, since that would require `T` to
    /// provide a second `Repr`-like type that's built up from `SecretHandle`s instead of `Wire`s.
    /// Instead, we store the `TWire` of the `Secret` gate, and use `<T as Secret>::set_from_lit`
    /// to copy a `Lit` `TWire` into the `Secret` `TWire`.
    secret: TWire<'a, T>,
    default: TWire<'a, T>,
}

impl<'a, T: Repr<'a> + Secret<'a> + ?Sized> TSecretHandle<'a, T> {
    pub fn new(secret: TWire<'a, T>, default: TWire<'a, T>) -> TSecretHandle<'a, T> {
        TSecretHandle { secret, default }
    }

    pub fn set(&self, bld: &Builder<'a>, val: T) {
        let lit = bld.lit(val);
        T::set_from_lit(&self.secret.repr, &lit.repr, true);
    }

    pub fn apply_default(&self) {
        T::set_from_lit(&self.secret.repr, &self.default.repr, false);
    }

    pub fn wire(&self) -> &TWire<'a, T> {
        &self.secret
    }
}

impl<'a, T: Repr<'a> + Secret<'a> + ?Sized> Drop for TSecretHandle<'a, T> {
    fn drop(&mut self) {
        self.apply_default();
    }
}

impl<'a, T> Clone for TSecretHandle<'a, T>
where T: Repr<'a> + Secret<'a>, T::Repr: Clone {
    fn clone(&self) -> Self {
        TSecretHandle {
            secret: self.secret.clone(),
            default: self.default.clone(),
        }
    }
}

impl<'a, 'b, T> Migrate<'a, 'b> for TSecretHandle<'a, T>
where
    T: for<'c> Repr<'c>,
    T: for<'c> Secret<'c>,
    <T as Repr<'a>>::Repr: Migrate<'a, 'b, Output = <T as Repr<'b>>::Repr>,
{
    type Output = TSecretHandle<'b, T>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> TSecretHandle<'b, T> {
        // Since `TSecretHandle` implements `Drop`, we can't safely move out of its fields.
        unsafe {
            let this = MaybeUninit::new(self);
            // Avoid `*this.as_ptr()` after we start moving out of the fields.
            let secret_ptr = &(*this.as_ptr()).secret as *const _;
            let default_ptr = &(*this.as_ptr()).default as *const _;
            TSecretHandle {
                secret: v.visit(ptr::read(secret_ptr)),
                default: v.visit(ptr::read(default_ptr)),
            }
        }
    }
}


pub trait Repr<'a> {
    type Repr;
}

pub trait Flatten<'a>: Repr<'a>
where <Self as Repr<'a>>::Repr: Sized {
    /// Compute a type that can be used to represent `Self` as a single `Wire`.
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a>;

    /// Convert a `TWire<Self>` to a single `Wire`, whose type is given by `wire_type`.
    fn to_wire(bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a>;

    /// Convert a single `Wire` back into a `TWire<Self>`.
    fn from_wire(bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self>;
}


pub trait Lit<'a>
where Self: Repr<'a> {
    fn lit(bld: &Builder<'a>, x: Self) -> Self::Repr;
}

pub trait Secret<'a>
where Self: Repr<'a> + Lit<'a> + Sized {
    fn secret(bld: &Builder<'a>) -> Self::Repr;
    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool);
}

impl<'a> Builder<'a> {
    pub fn lit<T: Lit<'a>>(&self, x: T) -> TWire<'a, T> {
        TWire::new(Lit::lit(self, x))
    }

    pub fn secret<T: Secret<'a> + Default>(&self) -> (TWire<'a, T>, TSecretHandle<'a, T>)
    where T::Repr: Clone {
        self.secret_default(T::default())
    }

    pub fn secret_default<T: Secret<'a>>(
        &self,
        default: T,
    ) -> (TWire<'a, T>, TSecretHandle<'a, T>)
    where T::Repr: Clone {
        let w = self.secret_uninit::<T>();
        let sh = TSecretHandle::new(w.clone(), self.lit(default));
        (w, sh)
    }

    pub fn secret_init<T: Secret<'a>, F>(&self, mk_val: F) -> TWire<'a, T>
    where F: FnOnce() -> T {
        let w = self.secret_uninit::<T>();
        if self.c.is_prover() {
            let lit = self.lit(mk_val());
            Builder::set_secret_from_lit(&w, &lit, true);
        }
        w
    }

    pub fn secret_uninit<T: Secret<'a>>(&self) -> TWire<'a, T> {
        TWire::new(<T as Secret>::secret(self))
    }

    pub fn neq_zero<T>(&self, x: TWire<'a, T>) -> TWire<'a, bool>
    where
    T: Repr<'a>,
    T: Eq<'a, Output=bool>,
    T: Lit<'a>,
    T: num_traits::Zero,
    {
        // TODO: Use custom gate.
        let c : TWire<'a, bool> = self.eq(x,self.lit(T::zero()));
        self.not(c)
    }

    pub fn set_secret_from_lit<T: Secret<'a>>(s: &TWire<'a, T>, val: &TWire<'a, T>, force: bool) {
        <T as Secret>::set_from_lit(&s.repr, &val.repr, force);
    }
}

pub trait FromEval<'a>
where Self: Repr<'a> + Sized {
    fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Self::Repr) -> Option<Self>;
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


pub trait Cast<'a, Target = Self>
where Self: Repr<'a>, Target: Repr<'a> {
    fn cast(
        bld: &Builder<'a>,
        x: Self::Repr,
    ) -> Target::Repr;
}

impl<'a> Builder<'a> {
    pub fn cast<T: Cast<'a, U>, U: Repr<'a>>(
        &self,
        x: TWire<'a, T>,
    ) -> TWire<'a, U> {
        TWire::new(<T as Cast<U>>::cast(self, x.repr))
    }
}


#[macro_export]
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

#[macro_export]
macro_rules! primitive_binary_impl {
    ($Op:ident :: $op:ident ($T:ty, $U:ty) -> $R:ty) => {
        impl<'a> $Op<'a, $U> for $T {
            type Output = $R;
            fn $op(bld: &Builder<'a>, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
                bld.circuit().$op(a, b)
            }
        }
    };
}

impl<'a> Repr<'a> for bool {
    type Repr = Wire<'a>;
}

impl<'a> Flatten<'a> for bool {
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> { c.ty(TyKind::BOOL) }
    fn to_wire(_bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr }
    fn from_wire(_bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        assert!(*w.ty == TyKind::BOOL);
        TWire::new(w)
    }
}

impl<'a> Lit<'a> for bool {
    fn lit(bld: &Builder<'a>, x: bool) -> Wire<'a> {
        bld.c.lit(bld.c.ty(TyKind::BOOL), x as u64)
    }
}

impl<'a> Secret<'a> for bool {
    fn secret(bld: &Builder<'a>) -> Wire<'a> {
        bld.c.new_secret_wire_uninit(bld.c.ty(TyKind::BOOL))
    }

    fn set_from_lit(s: &Wire<'a>, val: &Wire<'a>, force: bool) {
        s.kind.as_secret().set_from_lit(*val, force);
    }
}

impl<'a> FromEval<'a> for bool {
    fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Self::Repr) -> Option<Self> {
        let val = ev.eval_single_wire(a).ok()?;
        Some(!val.is_zero())
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

macro_rules! integer_cast_impl {
    ($T:ty, $U:ty, $K:ident) => {
        impl<'a> Cast<'a, $U> for $T {
            fn cast(bld: &Builder<'a>, x: Wire<'a>) -> Wire<'a> {
                bld.c.cast(x, bld.c.ty(TyKind::$K))
            }
        }
    };
}

macro_rules! integer_impls {
    ($T:ty, $K:ident) => {
        impl<'a> Repr<'a> for $T {
            type Repr = Wire<'a>;
        }

        impl<'a> Flatten<'a> for $T {
            fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> { c.ty(TyKind::$K) }
            fn to_wire(_bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr }
            fn from_wire(_bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                assert!(*w.ty == TyKind::$K);
                TWire::new(w)
            }
        }

        impl<'a> Lit<'a> for $T {
            fn lit(bld: &Builder<'a>, x: $T) -> Wire<'a> {
                bld.c.lit(bld.c.ty(TyKind::$K), x as u64)
            }
        }

        impl<'a> Secret<'a> for $T {
            fn secret(bld: &Builder<'a>) -> Wire<'a> {
                bld.c.new_secret_wire_uninit(bld.c.ty(TyKind::$K))
            }

            fn set_from_lit(s: &Wire<'a>, val: &Wire<'a>, force: bool) {
                s.kind.as_secret().set_from_lit(*val, force);
            }
        }

        impl<'a> FromEval<'a> for $T {
            fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Self::Repr) -> Option<Self> {
                let val = ev.eval_single_wire(a).ok()?;
                // Conversion should succeed, assuming `a` really carries a value of type `$T`.
                Some(<$T as TryFrom<_>>::try_from(val).unwrap())
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

        impl<'a> Cast<'a, $T> for bool {
            fn cast(bld: &Builder<'a>, x: Wire<'a>) -> Wire<'a> {
                bld.c.cast(x, bld.c.ty(TyKind::$K))
            }
        }

        integer_cast_impl!($T, i8, I8);
        integer_cast_impl!($T, i16, I16);
        integer_cast_impl!($T, i32, I32);
        integer_cast_impl!($T, i64, I64);
        integer_cast_impl!($T, u8, U8);
        integer_cast_impl!($T, u16, U16);
        integer_cast_impl!($T, u32, U32);
        integer_cast_impl!($T, u64, U64);
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

/// Convert `N` bytes to `ceil(N/4)` u32s.
/// ceil(N/4) = (N+3)/4
fn u8_to_u32<N>(a: GenericArray<u8,N>) -> GenericArray<u32,Quot<Sum<N,U3>,U4>>
where
    N: ArrayLength<u8>,
    N: std::ops::Add<U3>,
    Sum<N,U3>: std::ops::Div<U4>,
    Quot<Sum<N,U3>,U4>: ArrayLength<u32>,
{
    let mut res = GenericArray::default();

    for (i, chunk) in a.chunks(4).enumerate() {
        let bytes = chunk.try_into().unwrap_or({
            let mut s: [u8;4] = [0;4];

            // TODO: How do we copy the whole slice at once?
            for (j, b) in chunk.iter().enumerate() {
                s[j] = *b;
            }

            s
        });
        res[i] = u32::from_le_bytes(bytes);
    }
    res
}

/// Convert `ceil(N/4)` u32s to `N` bytes.
fn u32_to_u8<N>(a: &GenericArray<u32,Quot<Sum<N,U3>,U4>>) -> GenericArray<u8,N>
where
    N: ArrayLength<u8>,
    N: std::ops::Add<U3>,
    Sum<N,U3>: std::ops::Div<U4>,
    Quot<Sum<N,U3>,U4>: ArrayLength<u32>,
{
    let mut res = GenericArray::default();
    let mut pos = 0;

    for x32 in a {
        let bs = x32.to_le_bytes();

        // TODO: How do we copy the whole slice at once?
        res[pos] = bs[0]; pos += 1;
        if pos < res.len() {
            res[pos] = bs[1]; pos += 1;
        } else {
            break;
        }
        if pos < res.len() {
            res[pos] = bs[2]; pos += 1;
        } else {
            break;
        }
        if pos < res.len() {
            res[pos] = bs[3]; pos += 1;
        } else {
            break;
        }
    }

    res
}

macro_rules! field_impls {
    ($T:ty, $K:ident) => {
        impl<'a> Repr<'a> for $T {
            type Repr = Wire<'a>;
        }

        impl<'a> Flatten<'a> for $T {
            fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> { c.ty(TyKind::GF(Field::$K)) }
            fn to_wire(_bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr }
            fn from_wire(_bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                assert!(*w.ty == TyKind::GF(Field::$K));
                TWire::new(w)
            }
        }

        impl<'a> Lit<'a> for $T {
            fn lit(bld: &Builder<'a>, x: $T) -> Wire<'a> {
                bld.c.lit(bld.c.ty(TyKind::GF(Field::$K)), x)
            }
        }

        impl<'a> Secret<'a> for $T {
            fn secret(bld: &Builder<'a>) -> Wire<'a> {
                bld.c.new_secret_wire_uninit(bld.c.ty(TyKind::GF(Field::$K)))
            }

            fn set_from_lit(s: &Wire<'a>, val: &Wire<'a>, force: bool) {
                s.kind.as_secret().set_from_lit(*val, force);
            }
        }

        // impl<'a> FromEval<'a> for $T {
        //     fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Self::Repr) -> Option<Self> {
        //         // let val = ev.eval_single_wire(a).ok()?;
        //         // // Conversion should succeed, assuming `a` really carries a value of type `$T`.
        //         // Some(<$T as TryFrom<_>>::try_from(val).unwrap())
        //         unimplemented!{}
        //     }
        // }

        primitive_unary_impl!(Neg::neg($T));
        // primitive_unary_impl!(Not::not($T));
        primitive_binary_impl!(Add::add($T, $T) -> $T);
        primitive_binary_impl!(Sub::sub($T, $T) -> $T);
        primitive_binary_impl!(Mul::mul($T, $T) -> $T);
        // primitive_binary_impl!(Div::div($T, $T) -> $T);
        // primitive_binary_impl!(Mod::mod_($T, $T) -> $T);
        // primitive_binary_impl!(And::and($T, $T) -> $T);
        // primitive_binary_impl!(Or::or($T, $T) -> $T);
        // primitive_binary_impl!(Xor::xor($T, $T) -> $T);
        // primitive_binary_impl!(Shl::shl($T, u8) -> $T);
        // primitive_binary_impl!(Shr::shr($T, u8) -> $T);
        primitive_binary_impl!(Eq::eq($T, $T) -> bool);
        primitive_binary_impl!(Ne::ne($T, $T) -> bool);
        // primitive_binary_impl!(Lt::lt($T, $T) -> bool);
        // primitive_binary_impl!(Le::le($T, $T) -> bool);
        // primitive_binary_impl!(Gt::gt($T, $T) -> bool);
        // primitive_binary_impl!(Ge::ge($T, $T) -> bool);

        impl<'a> Mux<'a, bool> for $T {
            type Output = $T;
            fn mux(bld: &Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
                bld.c.mux(c, t, e)
            }
        }

        // impl<'a> Cast<'a, $T> for bool {
        //     fn cast(bld: &Builder<'a>, x: Wire<'a>) -> Wire<'a> {
        //         bld.c.cast(x, bld.c.ty(TyKind::GF(Field::$K)))
        //     }
        // }

        // integer_cast_impl!($T, i8, I8);
        // integer_cast_impl!($T, i16, I16);
        // integer_cast_impl!($T, i32, I32);
        // integer_cast_impl!($T, i64, I64);
        // integer_cast_impl!($T, u8, U8);
        // integer_cast_impl!($T, u16, U16);
        // integer_cast_impl!($T, u32, U32);
        // integer_cast_impl!($T, u64, U64);

        impl AsBits for $T {
            fn as_bits<'a>(&self, c: &CircuitBase<'a>, _width: IntSize) -> Bits<'a> {
                let bytes = self.to_bytes();
                c.intern_bits(&u8_to_u32(bytes))
            }
        }

        impl FromBits for $T {
            fn from_bits<'a>(b:Bits<'a>) -> Self {
                let b = b.0.try_into().expect("Error deserializing field from bits. Invalid length.");
                let arr = u32_to_u8::<<$T as FiniteField>::ByteReprLen>(b);
                Self::from_bytes(&arr)
                    .expect("Error deserializing field from bits")
            }
        }
    };
}

field_impls!(Gf40, F40b);
field_impls!(Gf45, F45b);
field_impls!(F56b, F56b);
field_impls!(F63b, F63b);
field_impls!(F64b, F64b);

macro_rules! tuple_impl {
    ($($A:ident $B:ident),*) => {
        impl<'a, $($A: Repr<'a>,)*> Repr<'a> for ($($A,)*) {
            type Repr = ($(TWire<'a, $A>,)*);
        }

        impl<'a, $($A: Flatten<'a>,)*> Flatten<'a> for ($($A,)*) {
            fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
                c.ty_bundle(&[$($A::wire_type(c),)*])
            }

            fn to_wire(bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
                #![allow(bad_style)]    // Capitalized variable names $A
                let ($($A,)*) = w.repr;
                bld.c.pack(&[$(Flatten::to_wire(bld, $A),)*])
            }

            fn from_wire(bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                let mut it = 0..;
                $( let $A = Flatten::from_wire(bld, bld.c.extract(w, it.next().unwrap())); )*
                let num_elems = it.next().unwrap();

                match *w.ty {
                    TyKind::Bundle(tys) => assert!(tys.len() == num_elems),
                    // If num_elems is zero, there are no `bld.c.extract` calls, so the type error
                    // won't be caught above.
                    _ => panic!("expected Bundle, not {:?}", w.ty),
                }

                TWire::new(($($A,)*))
            }
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
            fn secret(bld: &Builder<'a>) -> Self::Repr {
                #![allow(unused)]       // `bld` in the zero-element case
                ($(bld.secret_uninit::<$A>(),)*)
            }

            fn set_from_lit(
                s: &($(TWire<'a, $A>,)*),
                val: &($(TWire<'a, $A>,)*),
                force: bool,
            ) {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `ev` in the zero-element case
                let &($(ref $A,)*) = s;
                let &($(ref $B,)*) = val;
                $(
                    <$A as Secret>::set_from_lit(&$A.repr, &$B.repr, force);
                )*
            }
        }

        impl<'a, $($A: FromEval<'a>,)*> FromEval<'a> for ($($A,)*) {
            fn from_eval<E: Evaluator<'a>>(
                ev: &mut E,
                a: ($(TWire<'a, $A>,)*),
            ) -> Option<($($A,)*)> {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `ev` in the zero-element case
                let ($($A,)*) = a;
                Some(($($A::from_eval(ev, $A.repr)?,)*))
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

            impl<'a, A: Flatten<'a>> Flatten<'a> for [A; $n] {
                fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
                    c.ty_bundle(&[A::wire_type(c); $n])
                }

                fn to_wire(bld: &Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let a = MaybeUninit::<[TWire<A>; $n]>::new(w.repr);
                        let mut o = MaybeUninit::<[Wire; $n]>::uninit();

                        for i in 0 .. $n {
                            let a_val = (a.as_ptr() as *const TWire<A>).add(i).read();
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = Flatten::to_wire(bld, a_val);

                            (o.as_mut_ptr() as *mut Wire).add(i).write(o_val);
                        }

                        bld.c.pack(&o.assume_init())
                    }
                }

                fn from_wire(bld: &Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                    match *w.ty {
                        TyKind::Bundle(tys) => assert!(tys.len() == $n),
                        // If num_elems is zero, there are no `bld.c.extract` calls, so the type error
                        // won't be caught above.
                        _ => panic!("expected Bundle, not {:?}", w.ty),
                    }

                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let mut o = MaybeUninit::<[TWire<A>; $n]>::uninit();

                        for i in 0 .. $n {
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = A::from_wire(bld, bld.c.extract(w, i));

                            (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                        }

                        TWire::new(o.assume_init())
                    }
                }
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
                fn secret(bld: &Builder<'a>) -> [TWire<'a, A>; $n] {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let o_val = bld.secret_uninit::<A>();
                            (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                        }

                        o.assume_init()
                    }
                }

                fn set_from_lit(
                    s: &[TWire<'a, A>; $n],
                    val: &[TWire<'a, A>; $n],
                    force: bool,
                ) {
                    for (s, val) in s.iter().zip(val.iter()) {
                        <A as Secret>::set_from_lit(&s.repr, &val.repr, force);
                    }
                }
            }

            impl<'a, A: FromEval<'a>> FromEval<'a> for [A; $n] {
                fn from_eval<E: Evaluator<'a>>(
                    ev: &mut E,
                    a: [TWire<'a, A>; $n],
                ) -> Option<[A; $n]> {
                    // Can't `collect()` or `into_iter()` an array yet, which makes this difficult
                    // to implement without unnecessary allocation.
                    unsafe {
                        let a = MaybeUninit::new(a);
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let a_val = (a.as_ptr() as *const TWire<'a, A>).add(i).read();
                            // If this panics, the remaining elements of `a` and `b` will leak.
                            let o_val = A::from_eval(ev, a_val.repr)?;

                            (o.as_mut_ptr() as *mut A).add(i).write(o_val);
                        }

                        Some(o.assume_init())
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

impl<'a, A: FromEval<'a>> FromEval<'a> for Vec<A> {
    fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Vec<TWire<'a, A>>) -> Option<Vec<A>> {
        a.into_iter().map(|x| A::from_eval(ev, x.repr)).collect()
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

    pub fn index_with_default<I, T>(
        &self,
        arr: &[TWire<'a, T>],
        idx: TWire<'a, I>,
        default: TWire<'a, T>,
        mut mk_idx: impl FnMut(&Self, usize) -> TWire<'a, I>,
    ) -> TWire<'a, T>
    where
        I: Eq<'a, I>,
        I::Repr: Clone,
        T: Mux<'a, <I as Eq<'a, I>>::Output, T, Output = T>,
        T::Repr: Clone,
    {
        let mut val = default;
        for (i, x) in arr.iter().enumerate() {
            let eq = self.eq(idx.clone(), mk_idx(self, i));
            val = self.mux(eq, x.clone(), val);
        }
        val
    }

    /// Output a `val` from `vals` on which `check(val)` outputs `true`.  If all checks output
    /// false (or `vals` is empty), then this function outputs `default` instead.
    pub fn select<C, A>(
        &self,
        vals: &[TWire<'a, A>],
        default: TWire<'a, A>,
        mut check: impl FnMut(&TWire<'a, A>) -> TWire<'a, C>,
    ) -> TWire<'a, A>
    where
        C: Repr<'a>,
        A: Mux<'a, C, A, Output = A>,
        A::Repr: Clone,
    {
        let mut acc = default;
        for val in vals {
            let cond = check(val);
            acc = self.mux(cond, val.clone(), acc);
        }
        acc
    }
}


pub trait EvaluatorExt<'a> {
    fn eval_typed<T: FromEval<'a>>(&mut self, w: TWire<'a, T>) -> Option<T>;
}

impl<'a, E: Evaluator<'a>> EvaluatorExt<'a> for E {
    fn eval_typed<T: FromEval<'a>>(&mut self, w: TWire<'a, T>) -> Option<T> {
        T::from_eval(self, w.repr)
    }
}
