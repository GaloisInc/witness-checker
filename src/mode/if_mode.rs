use zk_circuit_builder::eval::Evaluator;
use zk_circuit_builder::ir::circuit::{CircuitBase, CircuitTrait, Ty, Wire, Bits};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::typed::{
    self, Builder, BuilderExt, EvaluatorExt, Flatten, FromEval, Lit, Mux, Repr, Secret, TWire,
    LazySecret, SecretDep,
};
use serde::{Deserialize, Deserializer};
use std::any::type_name;
use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;


#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    MemorySafety,
    LeakUninit1,
    LeakTainted,
}


// Thread-local storage for tracking the current mode

thread_local! {
    static CURRENT_MODE: Cell<Option<Mode>> = Cell::new(None);
}

struct ResetCurrentMode(Option<Mode>);

impl Drop for ResetCurrentMode {
    fn drop(&mut self) {
        CURRENT_MODE.with(|c| c.set(self.0));
    }
}

/// Run `f` with the current mode set to `m`.
///
/// This is unsafe because both entering and leaving this function can invalidate any `ModeProof`
/// tokens that currently exist.  Generally, this should be called once at top level, before any
/// `ModeProof`s are created, and the closure should only return once no more `ModeProof`s exist.
pub unsafe fn with_mode<F: FnOnce() -> R, R>(m: Mode, f: F) -> R {
    // Set the mode to `m`, and restore the previous mode on the way out.
    let _g = ResetCurrentMode(
        CURRENT_MODE.with(|c| c.replace(Some(m))),
    );
    f()
}

pub fn get_mode() -> Mode {
    CURRENT_MODE.with(|c| {
        c.get().unwrap_or_else(|| panic!("mode not yet initialized"))
    })
}


// Type-level enum of Mode predicates

pub struct MemorySafety;
pub struct LeakUninit1;
pub struct LeakTainted;
pub struct AnyTainted;

pub trait ModePred {
    fn check(m: Mode) -> bool;
}

impl ModePred for MemorySafety {
    fn check(m: Mode) -> bool { m == Mode::MemorySafety }
}

impl ModePred for LeakUninit1 {
    fn check(m: Mode) -> bool { m == Mode::LeakUninit1 }
}

impl ModePred for LeakTainted {
    fn check(m: Mode) -> bool { m == Mode::LeakTainted }
}

impl ModePred for AnyTainted {
    fn check(m: Mode) -> bool {
        m == Mode::LeakUninit1 ||
        m == Mode::LeakTainted
    }
}


// Tokens that carry a proof about the current mode.  These are used for safe unchecked access to
// `IfMode` fields.

/// If `P: IsModeProof<M>`, then a token of type `P` is proof that the current mode is `M`.
pub unsafe trait IsModeProof<M: ModePred> {
    fn as_mode_proof(self) -> ModeProof<M>;
}

/// A proof token indicating that the current mode is `M`.
pub struct ModeProof<M: ModePred> {
    _marker: PhantomData<*const M>,
}

unsafe impl<M: ModePred> IsModeProof<M> for ModeProof<M> {
    fn as_mode_proof(self) -> ModeProof<M> { self }
}

impl<M: ModePred> ModeProof<M> {
    pub unsafe fn new_unchecked() -> ModeProof<M> {
        ModeProof {
            _marker: PhantomData,
        }
    }

    /// Check whether `m` satisfies predicate `M`, and if so, return a proof of the fact.
    ///
    /// This is unsafe since `ModeProof<M>` encodes a proof something about the current mode, while
    /// `m` could be any `Mode` value.
    pub unsafe fn new_checked(m: Mode) -> Option<ModeProof<M>> {
        if M::check(m) {
            Some(Self::new_unchecked())
        } else {
            None
        }
    }
}

/// Check whether predicate `M` holds on the current mode.  Returns `Some(pf)` if it does, or
/// `None` otherwise.
pub fn check_mode<M: ModePred>() -> Option<ModeProof<M>> {
    unsafe { ModeProof::new_checked(get_mode()) }
}

pub fn is_mode<M: ModePred>() -> bool {
    check_mode::<M>().is_some()
}

unsafe impl IsModeProof<AnyTainted> for ModeProof<LeakUninit1> {
    fn as_mode_proof(self) -> ModeProof<AnyTainted> {
        unsafe { ModeProof::new_unchecked() }
    }
}

unsafe impl IsModeProof<AnyTainted> for ModeProof<LeakTainted> {
    fn as_mode_proof(self) -> ModeProof<AnyTainted> {
        unsafe { ModeProof::new_unchecked() }
    }
}


/// Equivalent to `T` if the current mode is `M`, or equivalent to `()` otherwise.
pub struct IfMode<M: ModePred, T> {
    /// Stores `Some(x)` if `M::check(get_mode()) == true`, or `None` otherwise.
    ///
    /// In other words, the discriminant of the `Option` explicitly stores the value of
    /// `M::check(get_mode())`.  This should be a win in most cases, since `T` will generally be a
    /// pointer (no space is wasted), and a null check is likely much faster than a read from TLS.
    inner: Option<T>,
    _marker: PhantomData<M>,
}

impl<M: ModePred, T> IfMode<M, T> {
    unsafe fn new_unchecked(x: Option<T>) -> IfMode<M, T> {
        IfMode {
            inner: x,
            _marker: PhantomData,
        }
    }

    pub fn new(f: impl FnOnce(ModeProof<M>) -> T) -> IfMode<M, T> {
        unsafe { Self::new_unchecked(check_mode::<M>().map(f)) }
    }

    pub fn some(_pf: &impl IsModeProof<M>, x: T) -> IfMode<M, T> {
        unsafe { Self::new_unchecked(Some(x)) }
    }

    pub fn none() -> IfMode<M, T> {
        unsafe { Self::new_unchecked(None) }
    }


    pub fn proof(&self) -> Option<ModeProof<M>> {
        unsafe {
            if self.inner.is_some() {
                Some(ModeProof::new_unchecked())
            } else {
                None
            }
        }
    }


    pub fn get<'a>(&'a self, _pf: &impl IsModeProof<M>) -> &'a T {
        self.inner.as_ref().unwrap()
    }

    pub fn get_mut<'a>(&'a mut self, _pf: &impl IsModeProof<M>) -> &'a mut T {
        self.inner.as_mut().unwrap()
    }

    pub fn unwrap(self, _pf: &impl IsModeProof<M>) -> T {
        self.inner.unwrap()
    }


    pub fn try_get<'a>(&'a self) -> Option<&'a T> {
        self.as_ref().try_unwrap()
    }

    pub fn try_get_mut<'a>(&'a mut self) -> Option<&'a mut T> {
        self.as_mut().try_unwrap()
    }

    pub fn try_unwrap(self) -> Option<T> {
        self.inner
    }


    pub fn as_ref<'a>(&'a self) -> IfMode<M, &'a T> {
        unsafe { IfMode::new_unchecked(self.inner.as_ref()) }
    }

    pub fn as_mut<'a>(&'a mut self) -> IfMode<M, &'a mut T> {
        unsafe { IfMode::new_unchecked(self.inner.as_mut()) }
    }


    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> IfMode<M, U> {
        self.map_with(|_p, x| f(x))
    }

    pub fn map_with<U>(self, f: impl FnOnce(ModeProof<M>, T) -> U) -> IfMode<M, U> {
        unsafe {
            let inner = self.inner.map(|x| {
                let pf = ModeProof::new_unchecked();
                f(pf, x)
            });
            IfMode::new_unchecked(inner)
        }
    }

    pub fn zip<U, V>(self, other: IfMode<M, U>, f: impl FnOnce(T, U) -> V) -> IfMode<M, V> {
        self.map_with(|p, x| f(x, other.unwrap(&p)))
    }
}


impl<M: ModePred, T: Clone> Clone for IfMode<M, T> {
    fn clone(&self) -> IfMode<M, T> {
        unsafe { Self::new_unchecked(self.inner.clone()) }
    }
}

impl<M: ModePred, T: Copy> Copy for IfMode<M, T> {}
// impl<'a, M: ModePred, A> Copy for IfMode<M, TWire<'a, A>> {}

impl<M: ModePred, T: PartialEq> PartialEq for IfMode<M, T> {
    fn eq(&self, other: &IfMode<M, T>) -> bool {
        self.inner == other.inner
    }

    fn ne(&self, other: &IfMode<M, T>) -> bool {
        self.inner != other.inner
    }
}

impl<M: ModePred, T: Eq> Eq for IfMode<M, T> {}

impl<'a, 'b, M: ModePred, T: Migrate<'a, 'b>> Migrate<'a, 'b> for IfMode<M, T> {
    type Output = IfMode<M, T::Output>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> IfMode<M, T::Output> {
        IfMode {
            inner: v.visit(self.inner),
            _marker: PhantomData,
        }
    }
}

/// Provides an implementation of IfMode that panics when in mode M, effectively requiring the
/// field to be provided.
pub fn panic_default<M: ModePred, T>() -> IfMode<M, T> {
    IfMode::<M, T>::new(|_pf| panic!("Invalid input. Missing corresponding field for {}.", type_name::<IfMode<M, T>>()))
}

impl<M: ModePred, T: fmt::Debug> fmt::Debug for IfMode<M, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        <Option<T> as fmt::Debug>::fmt(&self.inner, fmt)
    }
}

impl<M: ModePred, T: fmt::Display> fmt::Display for IfMode<M, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if let Some(x) = self.try_get() {
            x.fmt( fmt)
        } else {
            write!(fmt, "()")
        }
    }
}

impl<'de, M: ModePred, A: Deserialize<'de>> Deserialize<'de> for IfMode<M, A> {
    fn deserialize<D>(deserializer: D) -> Result<IfMode<M, A>, D::Error>
    where
        D: Deserializer<'de>,
    {
        if let Some(p) = check_mode() {
            Deserialize::deserialize(deserializer).map(|x| IfMode::some(&p, x))
        } else {
            // JP: Better combinator for this? map_with_or?
            Ok(IfMode::none())
        }
    }
}

impl<'a, M: ModePred, A: FromEval<'a> + Repr<'a>> FromEval<'a> for IfMode<M, A> {
    fn from_eval<E: Evaluator<'a> + ?Sized>(
        c: &CircuitBase<'a>,
        ev: &mut E,
        a: Self::Repr,
    ) -> Option<Self> {
        if let Some(pf) = check_mode() {
            let x = a.unwrap(&pf);
            ev.eval_typed(c, x).map(|r| IfMode::some(&pf, r))
        } else {
            // JP: Better combinator for this? map_with_or?
            Some(IfMode::none())
        }
    }
}

impl<'a, M: ModePred, A: Repr<'a>> Repr<'a> for IfMode<M, A> {
    type Repr = IfMode<M, TWire<'a, A>>;
    // type Repr = IfMode<M, A::Repr>;
}

impl<'a, M: ModePred, A: Flatten<'a>> Flatten<'a> for IfMode<M, A> {
    fn wire_type<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Ty<'a> {
        if check_mode::<M>().is_some() {
            A::wire_type(c)
        } else {
            <()>::wire_type(c)
        }
    }

    fn to_wire(bld: &impl Builder<'a>, w: TWire<'a, Self>) -> Wire<'a> {
        if let Some(w) = w.repr.try_unwrap() {
            A::to_wire(bld, w)
        } else {
            <()>::to_wire(bld, TWire::<()>::new(()))
        }
    }

    fn from_wire(bld: &impl Builder<'a>, w: Wire<'a>) -> TWire<'a, Self> {
        TWire::new(IfMode::new(|_| A::from_wire(bld, w)))
    }
}

impl<'a, M: ModePred, A: Lit<'a>> Lit<'a> for IfMode<M, A> {
    fn lit(bld: &impl Builder<'a>, x: IfMode<M, A>) -> IfMode<M, TWire<'a, A>> {
        x.map(|x| bld.lit(x))
    }
}

impl<'a, M: ModePred, A: Secret<'a>> Secret<'a> for IfMode<M, A> {
    fn secret(bld: &impl Builder<'a>) -> Self::Repr {
        IfMode::new(|_pf| bld.with_label("IfMode", || bld.secret_uninit()))
    }

    fn set_from_lit(s: &Self::Repr, val: &Self::Repr, force: bool) {
        if let Some(pf) = check_mode() {
            let s = s.get(&pf);
            let val = val.get(&pf);
            typed::set_secret_from_lit(&s, &val, force);
        }
    }
}

impl<'a, M: ModePred, C, T, E> Mux<'a, C, IfMode<M, E>> for IfMode<M, T>
where
    C: Repr<'a>,
    C::Repr: Clone,
    T: Mux<'a, C, E>,
    E: Repr<'a>,
{
    type Output = IfMode<M, <T as Mux<'a, C, E>>::Output>;
    fn mux(
        bld: &impl Builder<'a>,
        c: C::Repr,
        t: IfMode<M, TWire<'a, T>>,
        e: IfMode<M, TWire<'a, E>>,
    ) -> IfMode<M, TWire<'a, <T as Mux<'a, C, E>>::Output>> {
        t.zip(e, |t, e| bld.mux(TWire::<C>::new(c), t, e))
    }
}


impl<'a, M: ModePred, T: LazySecret<'a>> LazySecret<'a> for IfMode<M, T> {
    fn num_wires(sizes: &mut impl Iterator<Item = usize>) -> usize {
        if let Some(pf) = check_mode::<M>() {
            <T as LazySecret>::num_wires(sizes)
        } else {
            0
        }
    }

    fn build_repr_from_wires<C: CircuitTrait<'a> + ?Sized>(
        c: &C,
        sizes: &mut impl Iterator<Item = usize>,
        build_wire: &mut impl FnMut(Ty<'a>) -> Wire<'a>,
    ) -> Self::Repr {
        IfMode::new(|_pf| {
            TWire::new(T::build_repr_from_wires(c, sizes, build_wire))
        })
    }

    fn expected_word_len(sizes: &mut impl Iterator<Item = usize>) -> usize {
        if let Some(pf) = check_mode::<M>() {
            <T as LazySecret>::expected_word_len(sizes)
        } else {
            0
        }
    }
    fn word_len(&self) -> usize {
        if let Some(pf) = check_mode() {
            <T as LazySecret>::word_len(self.get(&pf))
        } else {
            0
        }
    }
    fn push_words(&self, out: &mut Vec<u32>) {
        if let Some(pf) = check_mode() {
            <T as LazySecret>::push_words(self.get(&pf), out);
        }
    }
}

impl<'a, M: ModePred, T: SecretDep<'a>> SecretDep<'a> for IfMode<M, T> {
    type Decoded = IfMode<M, T::Decoded>;
    fn num_wires(x: &Self::Repr) -> usize {
        if let Some(pf) = check_mode() {
            <T as SecretDep>::num_wires(x.get(&pf))
        } else {
            0
        }
    }
    fn for_each_wire(x: &Self::Repr, mut f: impl FnMut(Wire<'a>)) {
        if let Some(pf) = check_mode() {
            T::for_each_wire(x.get(&pf), f)
        }
    }
    fn num_sizes(x: &Self::Repr) -> usize {
        if let Some(pf) = check_mode() {
            T::num_sizes(x.get(&pf))
        } else {
            0
        }
    }
    fn for_each_size(x: &Self::Repr, f: impl FnMut(usize)) {
        if let Some(pf) = check_mode() {
            T::for_each_size(x.get(&pf), f)
        }
    }
    fn from_bits_iter(
        sizes: &mut impl Iterator<Item = usize>,
        bits: &mut impl Iterator<Item = Bits<'a>>,
    ) -> IfMode<M, T::Decoded> {
        IfMode::new(|_pf| {
            T::from_bits_iter(sizes, bits)
        })
    }
}
