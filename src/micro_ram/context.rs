use std::cell::RefCell;
use std::fmt;
use std::mem;

use crate::eval::{self, CachingEvaluator};
use crate::ir::circuit::Circuit;
use crate::ir::typed::{Builder, TWire, FromEval, EvaluatorExt};

#[macro_export]
macro_rules! wire_assert {
    ($cx:ident, $cond:expr, $($args:tt)*) => {
        {
            let cx = $cx;
            let cond = $cond;
            $cx.assert($cond, move |$cx| {
                eprintln!("invalid trace: {}", format_args!($($args)*));
            });
        }
    };

    (& $cx:ident, $cond:expr, $($args:tt)*) => {{
        let $cx = &$cx;
        wire_assert!($cx, $cond, $($args)*);
    }};
}

#[macro_export]
macro_rules! wire_bug_if {
    ($cx:ident, $cond:expr, $($args:tt)*) => {
        {
            let cx = $cx;
            let cond = $cond;
            $cx.bug_if($cond, move |$cx| {
                eprintln!("found bug: {}", format_args!($($args)*));
            });
        }
    };

    (& $cx:ident, $cond:expr, $($args:tt)*) => {{
        let $cx = &$cx;
        wire_bug_if!($cx, $cond, $($args)*);
    }};
}

pub struct SecretValue<T>(pub Option<T>);

impl<T> SecretValue<T> {
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> SecretValue<U> {
        SecretValue(self.0.map(f))
    }
}

impl<T: fmt::Display> fmt::Display for SecretValue<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(ref x) => fmt::Display::fmt(x, fmt),
            None => write!(fmt, "??"),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for SecretValue<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(ref x) => fmt::Debug::fmt(x, fmt),
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


struct Cond<'a> {
    c: TWire<'a, bool>,
    msg: Box<dyn FnOnce(&mut Context<'a>) + 'a>,
}

impl<'a> Cond<'a> {
    pub fn new(c: TWire<'a, bool>, msg: impl FnOnce(&mut Context<'a>) + 'a) -> Cond<'a> {
        Cond { c, msg: Box::new(msg) }
    }
}

pub struct Context<'a> {
    asserts: RefCell<Vec<Cond<'a>>>,
    bugs: RefCell<Vec<Cond<'a>>>,
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

    pub fn finish(mut self) -> (Vec<TWire<'a, bool>>, Vec<TWire<'a, bool>>) {
        let assert_conds = mem::take(&mut *self.asserts.borrow_mut());
        let asserts = assert_conds.into_iter()
            .map(|cond| {
                if self.assert_triggered(cond.c) == Some(true) {
                    (cond.msg)(&mut self);
                }
                cond.c
            })
            .collect();

        let bug_conds = mem::take(&mut *self.bugs.borrow_mut());
        let bugs = bug_conds.into_iter()
            .map(|cond| {
                if self.bug_triggered(cond.c) == Some(true) {
                    (cond.msg)(&mut self);
                }
                cond.c
            })
            .collect();

        (asserts, bugs)
    }

    /// Mark the execution as invalid if `cond` is false.  A failed assertion represents
    /// misbehavior on the part of the prover.
    pub fn assert(&self, cond: TWire<'a, bool>, msg: impl FnOnce(&mut Context<'a>) + 'a) {
        self.asserts.borrow_mut().push(Cond::new(cond, msg));
    }

    /// Signal an error condition of `cond` is true.  This should be used for situations like
    /// buffer overflows, which indicate a bug in the subject program.
    pub fn bug_if(&self, cond: TWire<'a, bool>, msg: impl FnOnce(&mut Context<'a>) + 'a) {
        self.bugs.borrow_mut().push(Cond::new(cond, msg));
    }

    pub fn when<R>(
        &self,
        b: &Builder<'a>,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_>) -> R,
    ) -> R {
        f(&ContextWhen { cx: self, b, path_cond })
    }

    fn assert_triggered(&self, cond: TWire<'a, bool>) -> Option<bool> {
        self.eval_raw(cond).map(|ok| !ok)
    }

    fn bug_triggered(&self, cond: TWire<'a, bool>) -> Option<bool> {
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

    pub fn assert(&self, cond: TWire<'a, bool>, msg: impl FnOnce(&mut Context<'a>) + 'a) {
        self.cx.assert(self.assert_cond(cond), msg);
    }

    pub fn bug_if(&self, cond: TWire<'a, bool>, msg: impl FnOnce(&mut Context<'a>) + 'a) {
        self.cx.bug_if(self.bug_cond(cond), msg);
    }

    pub fn when<R>(
        &self,
        b: &Builder<'a>,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_>) -> R,
    ) -> R {
        self.cx.when(b, b.and(self.path_cond, path_cond), f)
    }

    pub fn eval<T: FromEval<'a>>(&self, w: TWire<'a, T>) -> SecretValue<T> {
        self.cx.eval(w)
    }
}

