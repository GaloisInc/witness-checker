use std::cell::RefCell;
use std::fmt;

use crate::eval::{self, CachingEvaluator};
use crate::ir::circuit::Circuit;
use crate::ir::typed::{Builder, TWire, FromEval, EvaluatorExt};

#[macro_export]
macro_rules! wire_assert {
    ($cx:expr, $cond:expr, $($args:tt)*) => {
        {
            let cx = $cx;
            let cond = $cond;
            if cx.assert_triggered(cond) == Some(true) {
                eprintln!("invalid trace: {}", format_args!($($args)*));
            }
            $cx.assert($cond);
        }
    };
}

#[macro_export]
macro_rules! wire_bug_if {
    ($cx:expr, $cond:expr, $($args:tt)*) => {
        {
            let cx = $cx;
            let cond = $cond;
            if cx.bug_triggered(cond) == Some(true) {
                eprintln!("found bug: {}", format_args!($($args)*));
            }
            $cx.bug_if($cond);
        }
    };
}

pub struct SecretValue<T>(pub Option<T>);

impl<T: fmt::Display> fmt::Display for SecretValue<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(ref x) => fmt::Display::fmt(x, fmt),
            None => write!(fmt, "??"),
        }
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for SecretValue<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(ref x) => fmt::LowerHex::fmt(x, fmt),
            None => write!(fmt, "??"),
        }
    }
}

impl<T: fmt::UpperHex> fmt::UpperHex for SecretValue<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(ref x) => fmt::UpperHex::fmt(x, fmt),
            None => write!(fmt, "??"),
        }
    }
}


pub struct Context<'a> {
    asserts: RefCell<Vec<TWire<'a, bool>>>,
    bugs: RefCell<Vec<TWire<'a, bool>>>,
    eval: Option<RefCell<CachingEvaluator<'a, 'a, eval::RevealSecrets>>>,
}

impl<'a> Context<'a> {
    pub fn new(c: &'a Circuit<'a>) -> Context<'a> {
        Context {
            asserts: RefCell::new(Vec::new()),
            bugs: RefCell::new(Vec::new()),
            eval: Some(RefCell::new(CachingEvaluator::new(c))),
        }
    }

    pub fn finish(self) -> (Vec<TWire<'a, bool>>, Vec<TWire<'a, bool>>) {
        (
            self.asserts.into_inner(),
            self.bugs.into_inner(),
        )
    }

    /// Mark the execution as invalid if `cond` is false.  A failed assertion represents
    /// misbehavior on the part of the prover.
    pub fn assert(&self, cond: TWire<'a, bool>) {
        self.asserts.borrow_mut().push(cond);
    }

    /// Signal an error condition of `cond` is true.  This should be used for situations like
    /// buffer overflows, which indicate a bug in the subject program.
    pub fn bug_if(&self, cond: TWire<'a, bool>) {
        self.bugs.borrow_mut().push(cond);
    }

    pub fn when<R>(
        &self,
        b: &Builder<'a>,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_>) -> R,
    ) -> R {
        f(&ContextWhen { cx: self, b, path_cond })
    }

    pub fn assert_triggered(&self, cond: TWire<'a, bool>) -> Option<bool> {
        self.eval_raw(cond).map(|ok| !ok)
    }

    pub fn bug_triggered(&self, cond: TWire<'a, bool>) -> Option<bool> {
        self.eval_raw(cond)
    }

    fn eval_raw<T: FromEval<'a>>(&self, w: TWire<'a, T>) -> Option<T> {
        let eval = self.eval.as_ref()?;
        eval.borrow_mut().eval_typed(w)
    }

    pub fn eval<T: FromEval<'a>>(&self, w: TWire<'a, T>) -> SecretValue<T> {
        SecretValue(self.eval_raw(w))
    }
}

pub struct ContextWhen<'a, 'b> {
    cx: &'b Context<'a>,
    b: &'b Builder<'a>,
    path_cond: TWire<'a, bool>,
}

impl<'a, 'b> ContextWhen<'a, 'b> {
    pub fn assert_cond(&self, cond: TWire<'a, bool>) -> TWire<'a, bool> {
        // The assertion passes if either this `when` block is not taken, or `cond` is satisfied.
        self.b.or(self.b.not(self.path_cond), cond)
    }

    pub fn bug_cond(&self, cond: TWire<'a, bool>) -> TWire<'a, bool> {
        // The bug occurs if this `when` block is taken and `cond` is satisfied.
        self.b.and(self.path_cond, cond)
    }

    pub fn assert(&self, cond: TWire<'a, bool>) {
        self.cx.assert(self.assert_cond(cond));
    }

    pub fn bug_if(&self, cond: TWire<'a, bool>) {
        self.cx.bug_if(self.bug_cond(cond));
    }

    pub fn when<R>(
        &self,
        b: &Builder<'a>,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_>) -> R,
    ) -> R {
        self.cx.when(b, b.and(self.path_cond, path_cond), f)
    }

    pub fn assert_triggered(&self, cond: TWire<'a, bool>) -> Option<bool> {
        self.cx.assert_triggered(self.assert_cond(cond))
    }

    pub fn bug_triggered(&self, cond: TWire<'a, bool>) -> Option<bool> {
        self.cx.bug_triggered(self.bug_cond(cond))
    }

    pub fn eval<T: FromEval<'a>>(&self, w: TWire<'a, T>) -> SecretValue<T> {
        self.cx.eval(w)
    }
}

