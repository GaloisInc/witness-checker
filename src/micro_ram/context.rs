use std::cell::RefCell;
use std::fmt;
use std::mem;

use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::circuit::{CircuitTrait, CircuitExt};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::typed::{Builder, TWire, FromEval, EvaluatorExt};

#[macro_export]
macro_rules! wire_assert {
    ($cx:ident, $cond:expr, $($args:tt)*) => {
        {
            let cond = $cond;
            $cx.assert(cond, move |$cx| {
                let msg = format!("{}", format_args!($($args)*));
                // Suppress unused variable warning regarding $cx, without disabling the warning
                // for the entire block.
                let _ = $cx;
                msg
            });
        }
    };

    ($cx:ident = $cx_expr:expr, $cond:expr, $($args:tt)*) => {{
        let $cx = $cx_expr;
        wire_assert!($cx, $cond, $($args)*);
    }};

    (& $cx:ident, $cond:expr, $($args:tt)*) => {{
        let $cx = &$cx;
        wire_assert!($cx, $cond, $($args)*);
    }};
}

#[macro_export]
macro_rules! wire_bug_if {
    ($cx:ident, $cond:expr, $($args:tt)*) => {
        {
            let cond = $cond;
            $cx.bug_if(cond, move |$cx| {
                let msg = format!("{}", format_args!($($args)*));
                // Suppress unused variable warning regarding $cx, without disabling the warning
                // for the entire block.
                let _ = $cx;
                msg
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
    state: CondState<'a>,
}

enum CondState<'a> {
    /// The condition hasn't been checked yet.  If it fails, the callback will be used to produce
    /// the error message.
    Pending(Box<dyn FnOnce(&mut Context<'a>) -> String + 'a>),
    /// The condition was migrated before it could be checked.  It hasn't been checked
    /// (successfully) yet.  If it fails, the saved (incomplete) message will be printed.
    PendingMigrated(Box<str>),
    /// The condition was checked successfully.
    Reported,
    /// We're running in verifier mode, so no conditions can be checked.
    VerifierMode,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
enum CondKind {
    Assert,
    Bug,
}

impl<'a> Cond<'a> {
    pub fn new(
        c: TWire<'a, bool>,
        msg: impl FnOnce(&mut Context<'a>) -> String + 'a,
        is_prover: bool,
    ) -> Cond<'a> {
        let state = if is_prover {
            CondState::Pending(Box::new(msg))
        } else {
            CondState::VerifierMode
        };
        Cond { c, state }
    }

    fn try_report(
        mut self,
        cx: &mut Context<'a>,
        kind: CondKind,
        triggered: Option<bool>,
    ) -> Self {
        self.state = match self.state {
            CondState::Pending(msg_func) => match triggered {
                Some(true) => {
                    let msg = msg_func(cx);
                    eprintln!("{}: {}", kind.prefix(), msg);
                    CondState::Reported
                },
                Some(false) => CondState::Reported,
                None => {
                    let msg = msg_func(cx);
                    eprintln!(
                        "unable to determine validity (missing secret): {}: {}",
                        kind.prefix(), msg,
                    );
                    CondState::PendingMigrated(msg.into_boxed_str())
                },
            },
            CondState::PendingMigrated(msg) => match triggered {
                Some(true) => {
                    eprintln!("{}: {}", kind.prefix(), msg);
                    CondState::Reported
                },
                Some(false) => CondState::Reported,
                None => CondState::PendingMigrated(msg),
            }
            CondState::Reported => CondState::Reported,
            CondState::VerifierMode => CondState::VerifierMode,
        };
        self
    }
}

impl CondKind {
    fn prefix(self) -> &'static str {
        match self {
            CondKind::Assert => "invalid trace",
            CondKind::Bug => "found bug",
        }
    }
}

pub struct Context<'a> {
    asserts: RefCell<Vec<Cond<'a>>>,
    bugs: RefCell<Vec<Cond<'a>>>,
    eval: Option<RefCell<CachingEvaluator<'a, eval::RevealSecrets>>>,
    is_prover: bool,
}

impl<'a> Context<'a> {
    pub fn new<C: CircuitTrait<'a> + ?Sized>(c: &'a C) -> Context<'a> {
        Context {
            asserts: RefCell::new(Vec::new()),
            bugs: RefCell::new(Vec::new()),
            eval: Some(RefCell::new(CachingEvaluator::new(c))),
            is_prover: c.is_prover(),
        }
    }

    pub fn finish(mut self) -> (Vec<TWire<'a, bool>>, Vec<TWire<'a, bool>>) {
        let assert_conds = mem::take(&mut *self.asserts.borrow_mut());
        let asserts = assert_conds.into_iter().map(|cond| {
            let triggered = self.assert_triggered(cond.c);
            cond.try_report(&mut self, CondKind::Assert, triggered).c
        }).collect();

        let bug_conds = mem::take(&mut *self.bugs.borrow_mut());
        let bugs = bug_conds.into_iter().map(|cond| {
            let triggered = self.bug_triggered(cond.c);
            cond.try_report(&mut self, CondKind::Bug, triggered).c
        }).collect();

        (asserts, bugs)
    }

    /// Mark the execution as invalid if `cond` is false.  A failed assertion represents
    /// misbehavior on the part of the prover.
    pub fn assert(
        &self,
        cond: TWire<'a, bool>,
        msg: impl FnOnce(&mut Context<'a>) -> String + 'a,
    ) {
        self.asserts.borrow_mut().push(Cond::new(cond, msg, self.is_prover));
    }

    /// Signal an error condition of `cond` is true.  This should be used for situations like
    /// buffer overflows, which indicate a bug in the subject program.
    pub fn bug_if(
        &self,
        cond: TWire<'a, bool>,
        msg: impl FnOnce(&mut Context<'a>) -> String + 'a,
    ) {
        self.bugs.borrow_mut().push(Cond::new(cond, msg, self.is_prover));
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

impl<'a, 'b> Migrate<'a, 'b> for Context<'a> {
    type Output = Context<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(mut self, v: &mut V) -> Context<'b> {
        let asserts = mem::take(&mut self.asserts).into_inner().into_iter().map(|cond| {
            let triggered = self.assert_triggered(cond.c);
            let cond = cond.try_report(&mut self, CondKind::Assert, triggered);
            v.visit(cond)
        }).collect();

        let bugs = mem::take(&mut self.bugs).into_inner().into_iter().map(|cond| {
            let triggered = self.bug_triggered(cond.c);
            let cond = cond.try_report(&mut self, CondKind::Bug, triggered);
            v.visit(cond)
        }).collect();

        Context {
            asserts: RefCell::new(asserts),
            bugs: RefCell::new(bugs),
            eval: v.visit(self.eval),
            is_prover: self.is_prover,
        }
    }
}

impl<'a, 'b> Migrate<'a, 'b> for Cond<'a> {
    type Output = Cond<'b>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Cond<'b> {
        Cond {
            c: v.visit(self.c),
            state: match self.state {
                // The case that contains a `+ 'a` closure can't be migrated.
                CondState::Pending(_) => panic!("can't migrate a Cond in CondState::Pending"),
                // The remaining cases can be migrated to `'b` lifetime by deconstructing and
                // reconstructing them.
                CondState::PendingMigrated(msg) => CondState::PendingMigrated(msg),
                CondState::Reported => CondState::Reported,
                CondState::VerifierMode => CondState::VerifierMode,
            },
        }
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

    pub fn assert(
        &self,
        cond: TWire<'a, bool>,
        msg: impl FnOnce(&mut Context<'a>) -> String + 'a,
    ) {
        self.cx.assert(self.assert_cond(cond), msg);
    }

    pub fn bug_if(
        &self,
        cond: TWire<'a, bool>,
        msg: impl FnOnce(&mut Context<'a>) -> String + 'a,
    ) {
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

