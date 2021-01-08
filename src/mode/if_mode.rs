use crate::eval::Evaluator;
use crate::ir::typed::{self, Builder, FromEval, EvaluatorExt, Lit, Repr, TWire};
use serde::{Deserialize, Deserializer};
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

    pub fn some(_pf: &(impl IsModeProof<M>), x: T) -> IfMode<M, T> {
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

impl<M: ModePred, T: PartialEq> PartialEq for IfMode<M, T> {
    fn eq(&self, other: &IfMode<M, T>) -> bool {
        self.inner == other.inner
    }

    fn ne(&self, other: &IfMode<M, T>) -> bool {
        self.inner != other.inner
    }
}

impl<M: ModePred, T: Eq> Eq for IfMode<M, T> {}

impl<M: ModePred, T: Default> Default for IfMode<M, T> {
    fn default() -> IfMode<M, T> {
        Self::new(|_pf| T::default())
    }
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
    fn from_eval<E: Evaluator<'a>>(ev: &mut E, a: Self::Repr) -> Option<Self> {
        if let Some(pf) = check_mode() {
            let x = a.unwrap(&pf);
            ev.eval_typed(x).map(|r| IfMode::some(&pf, r))
        } else {
            // JP: Better combinator for this? map_with_or?
            Some(IfMode::none())
        }
    }
}

// impl<'a, M: ModePred, T: typed::Eq<'a, Output = bool>> typed::Eq<'a, IfMode<M, T>> for IfMode<M, T> {
//     type Output = bool;
// 
//     fn eq(bld: &Builder<'a>, a: Self::Repr, b: Self::Repr) -> <bool as Repr<'a>>::Repr {
//         if let Some(pf) = check_mode::<M>() {
//             let a = a.unwrap(&pf);
//             let b = b.unwrap(&pf);
//             T::eq(bld, a, b)
//         } else {
//             // bool::lit(bld, true)
//             // This should be unreachable, otherwise the mode is influencing the circuit when it
//             // shouldn't.
//             // Maybe it doesn't make sense to implement an Eq impl.
//             unreachable!{}
//         }
//     }
// }

