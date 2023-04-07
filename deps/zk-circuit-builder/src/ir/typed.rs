use std::any;
use std::cmp;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::mem::{self, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::ptr;
use generic_array::{ArrayLength, GenericArray};
use generic_array::typenum::{Sum, Quot, U3, U4};
use num_traits::Zero;
#[cfg(feature = "gf_scuttlebutt")]
use scuttlebutt::field::{FiniteField, Gf40, Gf45, F56b, F63b, F64b};
use crate::eval::Evaluator;
use crate::ir::circuit::{
    AsBits, Bits, CircuitBase, CircuitTrait, CircuitExt, DynCircuit, Field, FromBits, IntSize,
    Wire, Ty, TyKind, CellResetGuard, GateKind,
};
use crate::ir::migrate::{self, Migrate};


pub trait Builder<'a>: 'a + Sized {
    type Circuit: ?Sized + CircuitTrait<'a>;
    fn circuit(&self) -> &Self::Circuit;
}

pub trait BuilderExt<'a>: Builder<'a> {
    fn is_prover(&self) -> bool {
        self.circuit().is_prover()
    }

    fn scoped_label<T: fmt::Display>(&self, label: T) -> CellResetGuard<&'a str> {
        self.circuit().scoped_label(label)
    }

    fn with_label<T: fmt::Display, F: FnOnce() -> R, R>(&self, label: T, f: F) -> R {
        self.circuit().with_label(label, f)
    }

    fn lit<T: Lit<'a>>(&self, x: T) -> TWire<'a, T> {
        TWire::new(Lit::lit(self, x))
    }

    fn secret<T: Secret<'a> + Default>(&self) -> (TWire<'a, T>, TSecretHandle<'a, T>)
    where T::Repr: Clone {
        self.secret_default(T::default())
    }

    fn secret_default<T: Secret<'a>>(
        &self,
        default: T,
    ) -> (TWire<'a, T>, TSecretHandle<'a, T>)
    where T::Repr: Clone {
        let w = self.secret_uninit::<T>();
        let sh = TSecretHandle::new(w.clone(), self.lit(default));
        (w, sh)
    }

    fn secret_init<T: Secret<'a>, F>(&self, mk_val: F) -> TWire<'a, T>
    where F: FnOnce() -> T {
        let w = self.secret_uninit::<T>();
        if self.is_prover() {
            let lit = self.lit(mk_val());
            set_secret_from_lit(&w, &lit, true);
        }
        w
    }

    fn secret_uninit<T: Secret<'a>>(&self) -> TWire<'a, T> {
        TWire::new(<T as Secret>::secret(self))
    }

    fn secret_lazy<T, S, F>(&self, init: F) -> TWire<'a, T>
    where
        T: for<'b> LazySecret<'b>,
        S: 'static,
        F: Fn(&S) -> T + Sized + Copy + 'static,
    {
        self.secret_lazy_sized(&[], init)
    }

    /// Create a lazy secret.
    ///
    /// `sizes` gives the expected sizes of any dynamically-sized data structures (such as `Vec`s)
    /// within the constructed value of type `T`.  Vector lengths and wire counts are public
    /// information, and the `sizes` argument lets us know how many secret wires to construct when
    /// operating in verifier mode.  The required length of `sizes` and the interpretation of its
    /// elements depends on `T`.  For the common case where `T` is `Vec<U>` and `U` contains no
    /// other complex data structures, `sizes` should have a single element giving the length of
    /// the `Vec`.
    fn secret_lazy_sized<T, S, F>(&self, sizes: &[usize], init: F) -> TWire<'a, T>
    where
        T: for<'b> LazySecret<'b>,
        S: 'static,
        F: Fn(&S) -> T + Sized + Copy + 'static,
    {
        lazy_secret_common::<Self, T, _>(self, sizes, move |ty, expected_word_len| {
            self.circuit().secret_lazy(ty, move |c, s| {
                lazy_secret_init_bits(c, init(s), expected_word_len)
            })
        })
    }

    fn secret_lazy_derived<T, S, D, F>(&self, deps: TWire<'a, D>, init: F) -> TWire<'a, T>
    where
        T: for<'b> LazySecret<'b>,
        S: 'static,
        D: for<'b> SecretDep<'b>,
        F: for <'b> Fn(&S, <D as SecretDep<'b>>::Decoded) -> T + Sized + Copy + 'static,
    {
        self.secret_lazy_derived_sized(&[], deps, init)
    }

    fn secret_lazy_derived_sized<T, S, D, F>(
        &self,
        sizes: &[usize],
        deps: TWire<'a, D>,
        init: F,
    ) -> TWire<'a, T>
    where
        T: for<'b> LazySecret<'b>,
        S: 'static,
        D: for<'b> SecretDep<'b>,
        F: for <'b> Fn(&S, <D as SecretDep<'b>>::Decoded) -> T + Sized + Copy + 'static,
    {
        let (dep_wires, fixed_size) = lazy_secret_build_dep_wires::<_, D>(self.circuit(), deps);
        lazy_secret_common::<Self, T, _>(self, sizes, move |ty, expected_word_len| {
            self.circuit().secret_lazy_derived(ty, dep_wires, move |c, s, bs| {
                let dep_val = lazy_secret_deps_from_bits::<D>(fixed_size, bs);
                lazy_secret_init_bits(c, init(s, dep_val), expected_word_len)
            })
        })
    }

    fn secret_derived<T, D, F>(&self, deps: TWire<'a, D>, init: F) -> TWire<'a, T>
    where
        T: for<'b> LazySecret<'b>,
        D: for<'b> SecretDep<'b>,
        F: for <'b> Fn(<D as SecretDep<'b>>::Decoded) -> T + Sized + Copy + 'static,
    {
        self.secret_derived_sized(&[], deps, init)
    }

    fn secret_derived_sized<T, D, F>(
        &self,
        sizes: &[usize],
        deps: TWire<'a, D>,
        init: F,
    ) -> TWire<'a, T>
    where
        T: for<'b> LazySecret<'b>,
        D: for<'b> SecretDep<'b>,
        F: for <'b> Fn(<D as SecretDep<'b>>::Decoded) -> T + Sized + Copy + 'static,
    {
        let (dep_wires, fixed_size) = lazy_secret_build_dep_wires::<_, D>(self.circuit(), deps);
        lazy_secret_common::<Self, T, _>(self, sizes, move |ty, expected_word_len| {
            self.circuit().secret_derived(ty, dep_wires, move |c, bs| {
                let dep_val = lazy_secret_deps_from_bits::<D>(fixed_size, bs);
                lazy_secret_init_bits(c, init(dep_val), expected_word_len)
            })
        })
    }


    fn neq_zero<T>(&self, x: TWire<'a, T>) -> TWire<'a, bool>
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


    fn neg<A: Neg<'a>>(&self, a: TWire<'a, A>) -> TWire<'a, A::Output> {
        TWire::new(<A as Neg>::neg(self, a.repr))
    }

    fn not<A: Not<'a>>(&self, a: TWire<'a, A>) -> TWire<'a, A::Output> {
        TWire::new(<A as Not>::not(self, a.repr))
    }


    fn add<A: Add<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Add<B>>::add(self, a.repr, b.repr))
    }

    fn sub<A: Sub<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Sub<B>>::sub(self, a.repr, b.repr))
    }

    fn mul<A: Mul<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Mul<B>>::mul(self, a.repr, b.repr))
    }

    fn div<A: Div<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Div<B>>::div(self, a.repr, b.repr))
    }

    fn mod_<A: Mod<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Mod<B>>::mod_(self, a.repr, b.repr))
    }

    fn and<A: And<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as And<B>>::and(self, a.repr, b.repr))
    }

    fn or<A: Or<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Or<B>>::or(self, a.repr, b.repr))
    }

    fn xor<A: Xor<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Xor<B>>::xor(self, a.repr, b.repr))
    }

    fn shl<A: Shl<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Shl<B>>::shl(self, a.repr, b.repr))
    }

    fn shr<A: Shr<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Shr<B>>::shr(self, a.repr, b.repr))
    }

    fn eq<A: Eq<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Eq<B>>::eq(self, a.repr, b.repr))
    }

    fn ne<A: Ne<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Ne<B>>::ne(self, a.repr, b.repr))
    }

    fn lt<A: Lt<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Lt<B>>::lt(self, a.repr, b.repr))
    }

    fn le<A: Le<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Le<B>>::le(self, a.repr, b.repr))
    }

    fn gt<A: Gt<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Gt<B>>::gt(self, a.repr, b.repr))
    }

    fn ge<A: Ge<'a, B>, B: Repr<'a>>(
        &self,
        a: TWire<'a, A>,
        b: TWire<'a, B>,
    ) -> TWire<'a, A::Output> {
        TWire::new(<A as Ge<B>>::ge(self, a.repr, b.repr))
    }


    fn mux<C: Repr<'a>, T: Mux<'a, C, E>, E: Repr<'a>>(
        &self,
        c: TWire<'a, C>,
        t: TWire<'a, T>,
        e: TWire<'a, E>,
    ) -> TWire<'a, T::Output> {
        TWire::new(<T as Mux<C, E>>::mux(self, c.repr, t.repr, e.repr))
    }

    fn cast<T: Cast<'a, U>, U: Repr<'a>>(
        &self,
        x: TWire<'a, T>,
    ) -> TWire<'a, U> {
        TWire::new(<T as Cast<U>>::cast(self, x.repr))
    }


    fn mux_multi<C, A>(
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

    fn index<I, T>(
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

    fn index_with_default<I, T>(
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
    fn select<C, A>(
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

impl<'a, B: Builder<'a>> BuilderExt<'a> for B {}


fn lazy_secret_common<'a, B, T, F>(
    b: &B,
    sizes: &[usize],
    mut f: F,
) -> TWire<'a, T>
where
    B: Builder<'a>,
    T: for<'b> LazySecret<'b>,
    F: FnMut(Ty<'a>, usize) -> Wire<'a>,
{
    // This call will panic if there aren't enough entries in `sizes`.
    let num_wires = T::num_wires(&mut sizes.iter().copied());
    let expected_word_len = T::expected_word_len(&mut sizes.iter().copied());

    if num_wires == 1 {
        let r = T::build_repr_from_wires(b.circuit(), &mut sizes.iter().copied(), &mut |ty| {
            f(ty, expected_word_len)
        });
        TWire::new(r)
    } else {
        let cache = f(Ty::raw_bits(), expected_word_len);
        let cache_deps = b.circuit().wire_list(&[cache]);
        let mut pos = 0;
        let r = T::build_repr_from_wires(b.circuit(), &mut sizes.iter().copied(), &mut |ty| {
            let start = pos;
            pos += ty.digits();
            let end = pos;
            b.circuit().secret_derived(ty, cache_deps, move |c, bs| {
                let b = bs[0];
                c.intern_bits(&b.0[start .. end])
            })
        });
        debug_assert_eq!(pos, expected_word_len);
        TWire::new(r)
    }
}

fn lazy_secret_init_bits<'b, T: LazySecret<'b>>(
    c: &CircuitBase<'b>,
    x: T,
    expected_word_len: usize,
) -> Bits<'b> {
    let word_len = x.word_len();
    debug_assert_eq!(word_len, expected_word_len,
        "callback produced wrong number of words, with T = {}", any::type_name::<T>());
    let mut words = Vec::with_capacity(word_len);
    x.push_words(&mut words);
    c.intern_bits(&words)
}

fn lazy_secret_build_dep_wires<'b, C: CircuitTrait<'b> + ?Sized, D: SecretDep<'b>>(
    c: &C,
    deps: TWire<'b, D>,
) -> (&'b [Wire<'b>], bool) {
    let expect_num_wires = D::num_wires(&deps.repr);
    let expect_num_sizes = D::num_sizes(&deps.repr);
    let fixed_size = expect_num_sizes == 0;

    let mut dep_wires: Vec<Wire>;
    if fixed_size {
        dep_wires = Vec::with_capacity(expect_num_wires);
    } else {
        // For non-fixed-size `D`, we collect the `sizes` list from `deps` and add it as an
        // extra `RawBits` literal in order to pass it into the closure (which must be `Copy`
        // and `'static`, forbidding normal means of passing it in).
        dep_wires = Vec::with_capacity(1 + expect_num_wires);
        let mut sizes = Vec::with_capacity(expect_num_sizes);
        D::for_each_size(&deps.repr, |s| sizes.push(u32::try_from(s).unwrap()));
        debug_assert_eq!(sizes.len(), expect_num_sizes);
        let sizes = c.as_base().intern_bits(&sizes);
        let sizes_wire = c.gate(GateKind::Lit(sizes, Ty::raw_bits()));
        dep_wires.push(sizes_wire);
    }

    D::for_each_wire(&deps.repr, |w| dep_wires.push(w));
    debug_assert_eq!(dep_wires.len(), expect_num_wires + (if fixed_size { 0 } else { 1 }));
    let dep_wires = c.wire_list(&dep_wires);

    (dep_wires, fixed_size)
}

fn lazy_secret_deps_from_bits<'b, D: SecretDep<'b>>(
    fixed_size: bool,
    bs: &[Bits<'b>],
) -> D::Decoded {
    let mut it = bs.iter().copied();
    let dep_val = if fixed_size {
        D::from_bits_iter(&mut iter::empty(), &mut it)
    } else {
        let sizes = it.next().unwrap();
        D::from_bits_iter(
            &mut sizes.0.iter().map(|&x| usize::try_from(x).unwrap()),
            &mut it,
        )
    };
    debug_assert!(it.next().is_none());
    dep_val
}


pub fn set_secret_from_lit<'a, T: Secret<'a>>(s: &TWire<'a, T>, val: &TWire<'a, T>, force: bool) {
    <T as Secret>::set_from_lit(&s.repr, &val.repr, force);
}


#[repr(transparent)]
pub struct BuilderImpl<C>(C);

impl<C> BuilderImpl<C> {
    pub fn new(c: C) -> BuilderImpl<C> {
        BuilderImpl(c)
    }

    pub fn from_ref<'a>(c: &'a C) -> &'a BuilderImpl<C> {
        unsafe { mem::transmute(c) }
    }
}

impl<'a, C: CircuitTrait<'a> + 'a> Builder<'a> for BuilderImpl<C> {
    type Circuit = C;

    fn circuit(&self) -> &C {
        &self.0
    }
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

    pub fn set(&self, bld: &impl Builder<'a>, val: T) {
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
    fn to_wire(bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a>;

    /// Convert a single `Wire` back into a `TWire<Self>`.
    fn from_wire(bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self>;
}


pub trait Lit<'a>
where Self: Repr<'a> {
    fn lit(bld: &impl Builder<'a>, x: Self) -> Self::Repr;
}

pub trait Secret<'a>
where Self: Repr<'a> + Lit<'a> + Sized {
    fn secret(bld: &impl Builder<'a>) -> Self::Repr;
    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool);
}

pub trait FromEval<'a>
where Self: Repr<'a> + Sized {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Self::Repr,
    ) -> Option<Self>;
}

/// Types that support being used as the type of a lazy secret.
///
/// # Size parameters
///
/// Data structures such as `Vec<T>` are represented using a variable number of wires; that is, the
/// number of wires in the representation of a particular `Vec<T>` is known only dynamically.
/// However, these numbers are public information, since the prover and verifier must agree on the
/// number of wires in the circuit.  This means the verifier must have a way to construct a
/// `TWire<Vec<T>>` with the right number of elements, even though the values of those elements are
/// unknown.
///
/// To handle this, we introduce a notion of "size parameters", which describe the shape of a data
/// structure independent of the actual values it contains.  The `sizes` of a value is a sequence
/// of `usize`s, whose count and interpretation depends on the type.  The type `u32` has fixed
/// size; it is always represented using a single wire, so it requires no `sizes` to construct.
/// The type `Vec<u32>` requires one size parameter, which is the length of the vector;
/// constructing a `TWire<Vec<u32>>` with `sizes == &[5]` produces a vector containing 5 elements
/// of type `TWire<u32>`.
///
/// Both Rust values (of type `T`) and their circuit representations (of type `T::Repr`) have size
/// parameters.  A Rust value and its corresponding `TWire` always have identical shapes.  That is,
/// `x` and `bld.lit(x)` always have the same size parameters.
pub trait LazySecret<'a>
where Self: Repr<'a> {
    /// Get the number of wires required to represent a value of type `Self` with the indicated
    /// `sizes`.
    fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize;

    /// Build an instance of `Self::Repr` (with the indicated `sizes`) from a stream of individual
    /// wires.
    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr;

    /// Compute the expected length in words given the indicated `sizes`.
    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize;

    /// Count the number of `u32` words in the `Bits` representation of `self`.  This is always
    /// equal to the sum of the `digits()` length of the wire types for all wires in `Self::Repr`.
    fn word_len(&self) -> usize;

    /// Push the words of `self` onto `out`.  This always pushes exactly `self.word_len()` words.
    fn push_words(&self, out: &mut Vec<u32>);
}

/// Types tha support being used as dependencies of derived secrets.
pub trait SecretDep<'a>
where Self: Repr<'a> {
    type Decoded;
    fn num_wires(x: &Self::Repr) -> usize;
    /// Iterate over the wires that make up `x`.  This calls `f` exactly `num_wires(x)` times.
    fn for_each_wire(x: &Self::Repr, f: impl FnMut(Wire<'a>));
    fn num_sizes(x: &Self::Repr) -> usize;
    /// Iterate over the size parameters that describe the shape of `x`.  This calls `f` exactly
    /// `num_sizes(x)` times.
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize));
    /// Build a concrete instance of `Self` from the provided `bits` and `sizes`.
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Self::Decoded;
}


macro_rules! define_un_ops {
    (
        $( $Op:ident :: $op:ident; )*
    ) => {
        $(
            pub trait $Op<'a>: Repr<'a> {
                type Output: Repr<'a>;
                fn $op(bld: &impl Builder<'a>, a: Self::Repr) -> <Self::Output as Repr<'a>>::Repr;
            }
        )*
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
                    bld: &impl Builder<'a>,
                    a: Self::Repr,
                    b: Other::Repr,
                ) -> <Self::Output as Repr<'a>>::Repr;
            }
        )*
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
        bld: &impl Builder<'a>,
        c: Cond::Repr,
        t: Self::Repr,
        e: Other::Repr,
    ) -> <Self::Output as Repr<'a>>::Repr;
}


pub trait Cast<'a, Target = Self>
where Self: Repr<'a>, Target: Repr<'a> {
    fn cast(
        bld: &impl Builder<'a>,
        x: Self::Repr,
    ) -> Target::Repr;
}


#[macro_export]
macro_rules! primitive_unary_impl {
    ($Op:ident :: $op:ident ($T:ty)) => {
        impl<'a> $Op<'a> for $T {
            type Output = $T;
            fn $op(bld: &impl Builder<'a>, a: Wire<'a>) -> Wire<'a> {
                bld.circuit().$op(a)
            }
        }
    };
}

#[macro_export]
macro_rules! primitive_binary_impl {
    ($Op:ident :: $op:ident ($T:ty, $U:ty) -> $R:ty) => {
        impl<'a> $Op<'a, $U> for $T {
            type Output = $R;
            fn $op(bld: &impl Builder<'a>, a: Wire<'a>, b: Wire<'a>) -> Wire<'a> {
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
    fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr }
    fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        assert!(*w.ty == TyKind::BOOL);
        TWire::new(w)
    }
}

impl<'a> Lit<'a> for bool {
    fn lit(bld: &impl Builder<'a>, x: bool) -> Wire<'a> {
        bld.circuit().lit(bld.circuit().ty(TyKind::BOOL), x as u64)
    }
}

impl<'a> Secret<'a> for bool {
    fn secret(bld: &impl Builder<'a>) -> Wire<'a> {
        bld.circuit().new_secret_wire_uninit(bld.circuit().ty(TyKind::BOOL))
    }

    fn set_from_lit(s: &Wire<'a>, val: &Wire<'a>, force: bool) {
        s.kind.as_secret().set_from_lit(*val, force);
    }
}

impl<'a> FromEval<'a> for bool {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Self::Repr,
    ) -> Option<Self> {
        let val = ev.eval_single_integer_wire(c, a).ok()?;
        Some(!val.is_zero())
    }
}

impl<'a> LazySecret<'a> for bool {
    fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize { 1 }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        build_wire(Self::wire_type(c))
    }

    fn expected_word_len(_sizes: &mut impl Iterator<Item = usize>) -> usize { 1 }
    fn word_len(&self) -> usize { 1 }
    fn push_words(&self, out: &mut Vec<u32>) {
        out.push(*self as u32);
    }
}

impl<'a> SecretDep<'a> for bool {
    type Decoded = bool;
    fn num_wires(x: &Self::Repr) -> usize { 1 }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        f(*x);
    }
    fn num_sizes(x: &Self::Repr) -> usize { 0 }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {}
    fn from_bits_iter(
        _sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> bool {
        let bits = bits.next().unwrap();
        !bits.is_zero()
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
    fn mux(bld: &impl Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
        bld.circuit().mux(c, t, e)
    }
}

macro_rules! integer_cast_impl {
    ($T:ty, $U:ty, $K:ident) => {
        impl<'a> Cast<'a, $U> for $T {
            fn cast(bld: &impl Builder<'a>, x: Wire<'a>) -> Wire<'a> {
                bld.circuit().cast(x, bld.circuit().ty(TyKind::$K))
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
            fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr }
            fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                assert!(*w.ty == TyKind::$K);
                TWire::new(w)
            }
        }

        impl<'a> Lit<'a> for $T {
            fn lit(bld: &impl Builder<'a>, x: $T) -> Wire<'a> {
                bld.circuit().lit(bld.circuit().ty(TyKind::$K), x as u64)
            }
        }

        impl<'a> Secret<'a> for $T {
            fn secret(bld: &impl Builder<'a>) -> Wire<'a> {
                bld.circuit().new_secret_wire_uninit(bld.circuit().ty(TyKind::$K))
            }

            fn set_from_lit(s: &Wire<'a>, val: &Wire<'a>, force: bool) {
                s.kind.as_secret().set_from_lit(*val, force);
            }
        }

        impl<'a> FromEval<'a> for $T {
            fn from_eval<E: Evaluator<'a> + ?Sized>(
                c: &CircuitBase<'a>,
                ev: &mut E,
                a: Self::Repr,
            ) -> Option<Self> {
                let val = ev.eval_single_integer_wire(c, a).ok()?;
                // Conversion should succeed, assuming `a` really carries a value of type `$T`.
                Some(<$T as TryFrom<_>>::try_from(val).unwrap())
            }
        }

        impl<'a> LazySecret<'a> for $T {
            fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize { 1 }

            fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
                c: &C,
                sizes: &mut impl Iterator<Item = usize>,
                build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
            ) -> Self::Repr {
                build_wire(Self::wire_type(c))
            }

            fn expected_word_len(_sizes: &mut impl Iterator<Item = usize>) -> usize {
                TyKind::$K.digits()
            }

            fn word_len(&self) -> usize {
                TyKind::$K.digits()
            }

            fn push_words(&self, out: &mut Vec<u32>) {
                let bs = self.to_le_bytes();
                for i in (0 .. bs.len()).step_by(4) {
                    let mut word_bytes = [0; 4];
                    let n = cmp::min(bs.len() - i, 4);
                    word_bytes[..n].copy_from_slice(&bs[i .. i + n]);
                    out.push(u32::from_le_bytes(word_bytes));
                }
            }
        }

        impl<'a> SecretDep<'a> for $T {
            type Decoded = $T;
            fn num_wires(x: &Self::Repr) -> usize { 1 }
            fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
                f(*x);
            }
            fn num_sizes(x: &Self::Repr) -> usize { 0 }
            fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {}
            fn from_bits_iter(
                _sizes: &mut impl Iterator<Item = usize>,
                bits: &mut impl Iterator<Item = Bits<'a>>,
            ) -> $T {
                let bits = bits.next().unwrap();
                let mut bs = [0; mem::size_of::<$T>()];
                for i in (0 .. bs.len()).step_by(4) {
                    let word = match bits.0.get(i / 4) {
                        Some(&x) => x,
                        None => break,
                    };
                    let word_bytes: [u8; 4] = word.to_le_bytes();
                    let n = cmp::min(bs.len() - i, word_bytes.len());
                    bs[i .. i + n].copy_from_slice(&word_bytes[..n]);
                }
                <$T>::from_le_bytes(bs)
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
            fn mux(bld: &impl Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
                bld.circuit().mux(c, t, e)
            }
        }

        impl<'a> Cast<'a, $T> for bool {
            fn cast(bld: &impl Builder<'a>, x: Wire<'a>) -> Wire<'a> {
                bld.circuit().cast(x, bld.circuit().ty(TyKind::$K))
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
            s[..chunk.len()].copy_from_slice(chunk);

            s
        });
        res[i] = u32::from_le_bytes(bytes);
    }
    res
}

/// Convert `ceil(N/4)` u32s to `N` bytes.
/// Assumes that any remaining bytes in the last chunk of `a` are zero and are ignored.
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

        let remaining = res.len() - pos;
        let n = cmp::min(remaining, bs.len());
        res[pos .. pos + n].copy_from_slice(&bs[..n]);
        pos += n;
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
            fn to_wire(_bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> { w.repr }
            fn from_wire(_bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                assert!(*w.ty == TyKind::GF(Field::$K));
                TWire::new(w)
            }
        }

        impl<'a> Lit<'a> for $T {
            fn lit(bld: &impl Builder<'a>, x: $T) -> Wire<'a> {
                bld.circuit().lit(bld.circuit().ty(TyKind::GF(Field::$K)), x)
            }
        }

        impl<'a> Secret<'a> for $T {
            fn secret(bld: &impl Builder<'a>) -> Wire<'a> {
                bld.circuit().new_secret_wire_uninit(bld.circuit().ty(TyKind::GF(Field::$K)))
            }

            fn set_from_lit(s: &Wire<'a>, val: &Wire<'a>, force: bool) {
                s.kind.as_secret().set_from_lit(*val, force);
            }
        }

        impl<'a> FromEval<'a> for $T {
            fn from_eval<E: Evaluator<'a> + ?Sized>(
                c: &CircuitBase<'a>,
                ev: &mut E,
                a: Self::Repr,
            ) -> Option<Self> {
                let val = ev.eval_single_field_wire(c, a).ok()?;
                // Conversion should succeed, assuming `a` really carries a value of type `$T`.
                Some(<$T>::from_bits(Bits(&val)))
            }
        }

        primitive_unary_impl!(Neg::neg($T));
        primitive_binary_impl!(Add::add($T, $T) -> $T);
        primitive_binary_impl!(Sub::sub($T, $T) -> $T);
        primitive_binary_impl!(Mul::mul($T, $T) -> $T);
        primitive_binary_impl!(Eq::eq($T, $T) -> bool);
        primitive_binary_impl!(Ne::ne($T, $T) -> bool);

        impl<'a> Mux<'a, bool> for $T {
            type Output = $T;
            fn mux(bld: &impl Builder<'a>, c: Wire<'a>, t: Wire<'a>, e: Wire<'a>) -> Wire<'a> {
                bld.circuit().mux(c, t, e)
            }
        }

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

        impl<'a> LazySecret<'a> for $T {
            fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize { 1 }

            fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
                c: &C,
                sizes: &mut impl Iterator<Item = usize>,
                build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
            ) -> Self::Repr {
                build_wire(Self::wire_type(c))
            }

            fn expected_word_len(_sizes: &mut impl Iterator<Item = usize>) -> usize {
                TyKind::GF(Field::$K).digits()
            }

            fn word_len(&self) -> usize {
                TyKind::GF(Field::$K).digits()
            }

            fn push_words(&self, out: &mut Vec<u32>) {
                let bs = self.to_bytes();
                for i in (0 .. bs.len()).step_by(4) {
                    let mut word_bytes = [0; 4];
                    let n = cmp::min(bs.len() - i, 4);
                    word_bytes[..n].copy_from_slice(&bs[i .. i + n]);
                    out.push(u32::from_le_bytes(word_bytes));
                }
            }
        }

        impl<'a> SecretDep<'a> for $T {
            type Decoded = $T;
            fn num_wires(x: &Self::Repr) -> usize { 1 }
            fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
                f(*x);
            }
            fn num_sizes(x: &Self::Repr) -> usize { 0 }
            fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {}
            fn from_bits_iter(
                _sizes: &mut impl Iterator<Item = usize>,
                bits: &mut impl Iterator<Item = Bits<'a>>,
            ) -> $T {
                let bits = bits.next().unwrap();
                let mut bs = GenericArray::<u8, <$T as FiniteField>::ByteReprLen>::default();
                for (i, &word) in bits.0.iter().enumerate() {
                    let word_bytes = word.to_le_bytes();
                    let j = i * word_bytes.len();
                    let n = cmp::min(bs.len() - j, word_bytes.len());
                    if n == 0 {
                        // The evaluator may add extra zeros at the end for some types.
                        debug_assert!(bits.0[i..].iter().all(|&x| x == 0));
                        break;
                    }
                    bs[j .. j + n].copy_from_slice(&word_bytes);
                }
                <$T>::from_bytes(&bs).unwrap()
            }
        }
    };
}

#[cfg(feature = "gf_scuttlebutt")]
field_impls!(Gf40, F40b);
#[cfg(feature = "gf_scuttlebutt")]
field_impls!(Gf45, F45b);
#[cfg(feature = "gf_scuttlebutt")]
field_impls!(F56b, F56b);
#[cfg(feature = "gf_scuttlebutt")]
field_impls!(F63b, F63b);
#[cfg(feature = "gf_scuttlebutt")]
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

            fn to_wire(bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
                #![allow(bad_style)]    // Capitalized variable names $A
                let ($($A,)*) = w.repr;
                bld.circuit().pack(&[$(Flatten::to_wire(bld, $A),)*])
            }

            fn from_wire(bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                let mut it = 0..;
                $( let $A = Flatten::from_wire(
                        bld, bld.circuit().extract(w, it.next().unwrap())); )*
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
            fn lit(bld: &impl Builder<'a>, x: Self) -> Self::Repr {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `bld` in the zero-element case
                let ($($A,)*) = x;
                ($(bld.lit($A),)*)
            }
        }

        impl<'a, $($A: Secret<'a>,)*> Secret<'a> for ($($A,)*) {
            fn secret(bld: &impl Builder<'a>) -> Self::Repr {
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
            fn from_eval<E: Evaluator<'a> + ?Sized>(
                c: &CircuitBase<'a>,
                ev: &mut E,
                a: ($(TWire<'a, $A>,)*),
            ) -> Option<($($A,)*)> {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `ev` in the zero-element case
                let ($($A,)*) = a;
                Some(($($A::from_eval(c, ev, $A.repr)?,)*))
            }
        }

        impl<'a, $($A: LazySecret<'a>,)*> LazySecret<'a> for ($($A,)*) {
            fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
                0 $( + $A::num_wires(sizes) )*
            }
            fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
                c: &C,
                sizes: &mut impl Iterator<Item = usize>,
                build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
            ) -> Self::Repr {
                #![allow(unused)]       // Arguments are unused in the zero-element case
                (
                    $( TWire::<$A>::new($A::build_repr_from_wires(c, sizes, build_wire)), )*
                )
            }
            fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
                0 $( + $A::expected_word_len(sizes) )*
            }
            fn word_len(&self) -> usize {
                #![allow(bad_style)]    // Capitalized variable names $A
                let ($(ref $A,)*) = *self;
                0 $( + $A.word_len() )*
            }
            fn push_words(&self, out: &mut Vec<u32>) {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `out` in the zero-element case
                let ($(ref $A,)*) = *self;
                $( $A.push_words(out); )*
            }
        }

        impl<'a, $($A: SecretDep<'a>,)*> SecretDep<'a> for ($($A,)*) {
            type Decoded = ( $( $A::Decoded, )* );
            fn num_wires(x: &Self::Repr) -> usize {
                #![allow(bad_style)]    // Capitalized variable names $A
                let ($(ref $A,)*) = *x;
                0 $( + $A::num_wires(&$A.repr) )*
            }
            fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `f` in the zero-element case
                let ($(ref $A,)*) = *x;
                $( $A::for_each_wire($A, |w| f(w)); )*
            }
            fn num_sizes(x: &Self::Repr) -> usize {
                #![allow(bad_style)]    // Capitalized variable names $A
                let ($(ref $A,)*) = *x;
                0 $( + $A::num_sizes(&$A.repr) )*
            }
            fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
                #![allow(bad_style)]    // Capitalized variable names $A
                #![allow(unused)]       // `f` in the zero-element case
                let ($(ref $A,)*) = *x;
                $( $A::for_each_size($A, |w| f(w)); )*
            }
            fn from_bits_iter(
                sizes: &mut impl Iterator<Item = usize>,
                bits: &mut impl Iterator<Item = Bits<'a>>,
            ) -> Self::Decoded {
                #![allow(unused)]       // Arguments are unused in the zero-element case
                (
                    $( $A::from_bits_iter(sizes, bits), )*
                )
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
                bld: &impl Builder<'a>,
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

                fn to_wire(bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
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

                        bld.circuit().pack(&o.assume_init())
                    }
                }

                fn from_wire(bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
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
                            let o_val = A::from_wire(bld, bld.circuit().extract(w, i));

                            (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                        }

                        TWire::new(o.assume_init())
                    }
                }
            }

            impl<'a, A: Lit<'a>> Lit<'a> for [A; $n] {
                fn lit(bld: &impl Builder<'a>, a: [A; $n]) -> [TWire<'a, A>; $n] {
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
                fn secret(bld: &impl Builder<'a>) -> [TWire<'a, A>; $n] {
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
                fn from_eval<E: Evaluator<'a> + ?Sized>(
                    c: &CircuitBase<'a>,
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
                            let o_val = A::from_eval(c, ev, a_val.repr)?;

                            (o.as_mut_ptr() as *mut A).add(i).write(o_val);
                        }

                        Some(o.assume_init())
                    }
                }
            }

            impl<'a, A: LazySecret<'a>> LazySecret<'a> for [A; $n] {
                fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
                    // `$n * A::num_wires(sizes)` is wrong because each array element of a type
                    // like `[Vec<T>; 3]` may have a different size.
                    (0 .. $n).map(|_| A::num_wires(sizes)).sum()
                }
                fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
                    c: &C,
                    sizes: &mut impl Iterator<Item = usize>,
                    build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
                ) -> Self::Repr {
                    unsafe {
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let o_val = TWire::<A>::new(
                                A::build_repr_from_wires(c, sizes, build_wire),
                            );
                            (o.as_mut_ptr() as *mut TWire<A>).add(i).write(o_val);
                        }

                        o.assume_init()
                    }
                }
                fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
                    (0 .. $n).map(|_| A::expected_word_len(sizes)).sum()
                }
                fn word_len(&self) -> usize {
                    self.iter().map(|x| x.word_len()).sum()
                }
                fn push_words(&self, out: &mut Vec<u32>) {
                    for x in self.iter() {
                        x.push_words(out);
                    }
                }
            }

            impl<'a, A: SecretDep<'a>> SecretDep<'a> for [A; $n] {
                type Decoded = [A::Decoded; $n];
                fn num_wires(x: &Self::Repr) -> usize {
                    x.iter().map(|tw| A::num_wires(&tw.repr)).sum()
                }
                fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
                    for y in x.iter() {
                        A::for_each_wire(y, |w| f(w));
                    }
                }
                fn num_sizes(x: &Self::Repr) -> usize {
                    x.iter().map(|tw| A::num_sizes(&tw.repr)).sum()
                }
                fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
                    for y in x.iter() {
                        A::for_each_size(y, |w| f(w));
                    }
                }
                fn from_bits_iter(
                    sizes: &mut impl Iterator<Item = usize>,
                    bits: &mut impl Iterator<Item = Bits<'a>>,
                ) -> [A::Decoded; $n] {
                    unsafe {
                        let mut o = MaybeUninit::uninit();

                        for i in 0 .. $n {
                            let o_val = A::from_bits_iter(sizes, bits);
                            (o.as_mut_ptr() as *mut A::Decoded).add(i).write(o_val);
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
                    bld: &impl Builder<'a>,
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
    fn lit(bld: &impl Builder<'a>, a: Vec<A>) -> Vec<TWire<'a, A>> {
        a.into_iter().map(|x| bld.lit(x)).collect()
    }
}

impl<'a, A: FromEval<'a>> FromEval<'a> for Vec<A> {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Vec<TWire<'a, A>>,
    ) -> Option<Vec<A>> {
        a.into_iter().map(|x| A::from_eval(c, ev, x.repr)).collect()
    }
}

// No `impl Secret for Vec<A>`, since we can't determine how many wires to create in the case where
// the value is unknown.

impl<'a, A: LazySecret<'a>> LazySecret<'a> for Vec<A> {
    fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        let n = sizes.next().unwrap();
        (0 .. n).map(|_| A::num_wires(sizes)).sum()
    }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        let n = sizes.next().unwrap();
        iter::repeat_with(|| {
            TWire::<A>::new(A::build_repr_from_wires(c, sizes, build_wire))
        }).take(n).collect()
    }

    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        let n = sizes.next().unwrap();
        (0 .. n).map(|_| A::expected_word_len(sizes)).sum()
    }
    fn word_len(&self) -> usize {
        self.iter().map(A::word_len).sum()
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        for x in self {
            x.push_words(out);
        }
    }
}

impl<'a, A: SecretDep<'a>> SecretDep<'a> for Vec<A> {
    type Decoded = Vec<A::Decoded>;
    fn num_wires(x: &Self::Repr) -> usize {
        x.iter().map(|tw| A::num_wires(&tw.repr)).sum()
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        for tw in x {
            A::for_each_wire(&tw.repr, |w| f(w))
        }
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        1 + x.iter().map(|tw| A::num_sizes(&tw.repr)).sum::<usize>()
    }
    fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
        f(x.len());
        for tw in x {
            A::for_each_size(&tw.repr, |s| f(s))
        }
    }
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Vec<A::Decoded> {
        let n = sizes.next().unwrap();
        iter::repeat_with(|| A::from_bits_iter(sizes, bits)).take(n).collect()
    }
}

impl<'a, C, A, B> Mux<'a, C, Vec<B>> for Vec<A>
where
    C: Repr<'a>,
    C::Repr: Clone,
    A: Repr<'a> + Mux<'a, C, B>,
    B: Repr<'a>,
{
    type Output = Vec<A::Output>;

    fn mux(
        bld: &impl Builder<'a>,
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


impl<'a, A: Repr<'a>> Repr<'a> for Option<A> {
    type Repr = Option<TWire<'a, A>>;
}

impl<'a, A: Lit<'a>> Lit<'a> for Option<A> {
    fn lit(bld: &impl Builder<'a>, a: Option<A>) -> Option<TWire<'a, A>> {
        a.map(|x| bld.lit(x))
    }
}

impl<'a, A: FromEval<'a>> FromEval<'a> for Option<A> {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Option<TWire<'a, A>>,
    ) -> Option<Option<A>> {
        a.map(|x| A::from_eval(c, ev, x.repr))
    }
}

// No `impl Secret for Option<A>`, since we can't determine how many wires to create in the case
// where the value is unknown.

impl<'a, A: LazySecret<'a>> LazySecret<'a> for Option<A> {
    fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        let n = sizes.next().unwrap();
        if n == 0 {
            0
        } else {
            A::num_wires(sizes)
        }
    }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        let n = sizes.next().unwrap();
        if n == 0 {
            None
        } else {
            Some(TWire::new(A::build_repr_from_wires(c, sizes, build_wire)))
        }
    }

    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        let n = sizes.next().unwrap();
        if n == 0 {
            0
        } else {
            A::expected_word_len(sizes)
        }
    }
    fn word_len(&self) -> usize {
        self.as_ref().map_or(0, A::word_len)
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        if let Some(x) = self.as_ref() {
            x.push_words(out);
        }
    }
}

impl<'a, A: SecretDep<'a>> SecretDep<'a> for Option<A> {
    type Decoded = Option<A::Decoded>;
    fn num_wires(x: &Self::Repr) -> usize {
        x.as_ref().map_or(0, |tw| A::num_wires(&tw.repr))
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        if let Some(tw) = x.as_ref() {
            A::for_each_wire(&tw.repr, |w| f(w))
        }
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        1 + x.as_ref().map_or(0, |tw| A::num_sizes(&tw.repr))
    }
    fn for_each_size(x: &Self::Repr, mut f: impl FnMut(usize)) {
        f(x.is_some() as usize);
        if let Some(tw) = x.as_ref() {
            A::for_each_size(&tw.repr, |s| f(s))
        }
    }
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Option<A::Decoded> {
        let n = sizes.next().unwrap();
        if n == 0 {
            None
        } else {
            Some(A::from_bits_iter(sizes, bits))
        }
    }
}


/// Wrapper type that flattens a value of type `T` into a single `Bits` value.  This is useful for
/// temporary values used in the computation of secrets which would otherwise be inefficient to
/// represent as separate wires.  You can build a lazy secret of type `TWire<FlatBits<T>>`, which
/// will be computed only once, then derive further secrets from it.
pub struct FlatBits<T>(pub T);

impl<'a, T> Repr<'a> for FlatBits<T> {
    type Repr = Wire<'a>;
}

impl<'a, T: LazySecret<'a>> Lit<'a> for FlatBits<T> {
    fn lit(bld: &impl Builder<'a>, x: FlatBits<T>) -> Wire<'a> {
        let mut words = Vec::with_capacity(T::word_len(&x.0));
        T::push_words(&x.0, &mut words);
        let bits = bld.circuit().as_base().intern_bits(&words);
        bld.circuit().lit(Ty::raw_bits(), bits)
    }
}

impl<'a, T: LazySecret<'a>> LazySecret<'a> for FlatBits<T> {
    fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize { 1 }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        build_wire(Ty::raw_bits())
    }

    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        T::expected_word_len(sizes)
    }
    fn word_len(&self) -> usize {
        T::word_len(&self.0)
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        T::push_words(&self.0, out);
    }
}

impl<'a, T: SecretDep<'a>> SecretDep<'a> for FlatBits<T> {
    type Decoded = FlatBits<T::Decoded>;
    fn num_wires(x: &Self::Repr) -> usize { 1 }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        f(*x);
    }
    fn num_sizes(x: &Self::Repr) -> usize { 0 }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {}
    fn from_bits_iter(
        _sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> FlatBits<T::Decoded> {
        // Provide no sizes and exactly one `Bits` to `T::from_bits_iter`.
        let bits = bits.next().unwrap();
        let x = T::from_bits_iter(&mut iter::empty(), &mut iter::once(bits));
        FlatBits(x)
    }
}

// TODO: add a `SizedRawBits<T>` for use with `Vec<T>` etc


/// Wire type used to obtain raw `Bits<'a>` for a dependency within `secret_derived`.
pub struct RawBits;

impl<'a> Repr<'a> for RawBits {
    type Repr = Wire<'a>;
}

impl<'a> Lit<'a> for RawBits {
    fn lit(bld: &impl Builder<'a>, _x: RawBits) -> Wire<'a> {
        bld.circuit().gate(GateKind::Lit(Bits::zero(), Ty::raw_bits()))
    }
}

impl<'a> SecretDep<'a> for RawBits {
    type Decoded = Bits<'a>;
    fn num_wires(x: &Self::Repr) -> usize { 1 }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        f(*x);
    }
    fn num_sizes(x: &Self::Repr) -> usize { 0 }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {}
    fn from_bits_iter(
        _sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> Bits<'a> {
        bits.next().unwrap()
    }
}

impl<'a, T> Cast<'a, RawBits> for FlatBits<T> {
    fn cast(_bld: &impl Builder<'a>, x: Wire<'a>) -> Wire<'a> {
        x
    }
}


pub trait EvaluatorExt<'a> {
    fn eval_typed<C: CircuitTrait<'a> + ?Sized, T: FromEval<'a>>(
        &mut self,
        c: &C,
        w: TWire<'a, T>,
    ) -> Option<T>;
}

impl<'a, E: Evaluator<'a> + ?Sized> EvaluatorExt<'a> for E {
    fn eval_typed<C: CircuitTrait<'a> + ?Sized, T: FromEval<'a>>(
        &mut self,
        c: &C,
        w: TWire<'a, T>,
    ) -> Option<T> {
        T::from_eval(c.as_base(), self, w.repr)
    }
}


#[cfg(test)]
mod test {
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::{Arenas, Circuit, FilterNil};
    use super::*;

    #[test]
    fn lazy_secret_int() {
        let arenas = Arenas::new();
        let c = Circuit::new::<u32>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::with_secret(&12345_u32);

        let w = b.secret_lazy(|&x: &u32| {
            assert_eq!(x, 12345);
            (x / 100) as u16
        });
        assert!(matches!(w.kind, GateKind::Secret(..)));
        let v: u16 = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v, 123);
    }

    #[test]
    fn derived_secret_int() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let a = b.add(b.lit(12300_u32), b.lit(45_u32));
        let w = b.secret_derived(a, |x: u32| {
            assert_eq!(x, 12345);
            (x / 100) as u16
        });
        assert!(matches!(w.kind, GateKind::Secret(..)));
        let v: u16 = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v, 123);
    }

    #[test]
    fn lazy_secret_pair() {
        let arenas = Arenas::new();
        let c = Circuit::new::<u32>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::with_secret(&12345_u32);

        let w = b.secret_lazy(|&x: &u32| {
            assert_eq!(x, 12345);
            (x as u64 * 1_000_000_000, (x / 100) as u16)
        });
        assert!(matches!(w.0.kind, GateKind::Secret(..)));
        assert!(matches!(w.1.kind, GateKind::Secret(..)));
        let (v0, v1): (u64, u16) = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v0, 12345_000_000_000);
        assert_eq!(v1, 123);
    }

    #[test]
    fn derived_secret_pair() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let a = b.lit((12300_u32, 45_u64));
        let w = b.secret_derived(a, |(x, y): (u32, u64)| {
            assert_eq!(x, 12300);
            assert_eq!(y, 45);
            x as u16 + y as u16
        });
        assert!(matches!(w.kind, GateKind::Secret(..)));
        let v: u16 = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v, 12345);
    }

    #[test]
    fn lazy_secret_vec() {
        let arenas = Arenas::new();
        let c = Circuit::new::<u32>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::with_secret(&12345_u32);

        let w = b.secret_lazy_sized(&[3], |&x: &u32| {
            assert_eq!(x, 12345);
            vec![x / 10000, x / 100 % 100, x % 100]
        });
        let v: Vec<u32> = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v, vec![1, 23, 45]);
    }

    #[test]
    fn derived_secret_vec() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let a = b.lit(vec![123_u32, 45]);
        let w = b.secret_derived_sized(&[3], a, |x: Vec<u32>| {
            assert_eq!(x, vec![123, 45]);
            vec![x[0] / 100, x[0] % 100, x[1]]
        });
        let v: Vec<u32> = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v, vec![1, 23, 45]);
    }

    #[test]
    fn small_secret_dep() {
        let arenas = Arenas::new();
        let c = Circuit::new::<()>(&arenas, true, FilterNil);
        let b = BuilderImpl::from_ref(&c);
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

        let a = TWire::<(_, _)>::new((b.lit(12300_u16), b.lit(45_u8)));
        let w = b.secret_derived(a, |(x, y)| {
            assert_eq!(x, 12300);
            assert_eq!(y, 45);
            x + y as u16
        });
        assert!(matches!(w.kind, GateKind::Secret(..)));
        let v: u16 = ev.eval_typed(&c, w).unwrap();
        assert_eq!(v, 12345);
    }
}
