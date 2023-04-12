use std::cell::RefCell;
use std::fmt;
use std::mem;

use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::circuit::{CircuitBase, CircuitTrait, CircuitExt, GateKind};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::typed::{Builder, BuilderExt, TWire, FromEval, EvaluatorExt};


#[macro_export]
macro_rules! wire_assert {
    ($cx:ident, $b:expr, $cond:expr, $($args:tt)*) => {
        {
            let cond = $cond;
            $cx.assert($b, cond, move |$cx| {
                let msg = format!("{}", format_args!($($args)*));
                // Suppress unused variable warning regarding $cx, without disabling the warning
                // for the entire block.
                let _ = $cx;
                msg
            });
        }
    };

    ($cx:ident = $cx_expr:expr, $b:expr, $cond:expr, $($args:tt)*) => {{
        let $cx = $cx_expr;
        wire_assert!($cx, $b, $cond, $($args)*);
    }};

    (& $cx:ident, $b:expr, $cond:expr, $($args:tt)*) => {{
        let $cx = &$cx;
        wire_assert!($cx, $b, $cond, $($args)*);
    }};
}

#[macro_export]
macro_rules! wire_bug_if {
    ($cx:ident, $b:expr, $cond:expr, $($args:tt)*) => {
        {
            let cond = $cond;
            $cx.bug_if($b, cond, move |$cx| {
                let msg = format!("{}", format_args!($($args)*));
                // Suppress unused variable warning regarding $cx, without disabling the warning
                // for the entire block.
                let _ = $cx;
                msg
            });
        }
    };

    (& $cx:ident, $b:expr, $cond:expr, $($args:tt)*) => {{
        let $cx = &$cx;
        wire_bug_if!($cx, $b, $cond, $($args)*);
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


#[derive(Migrate)]
pub struct Context<'a> {
    asserts: RefCell<Vec<TWire<'a, bool>>>,
    bugs: RefCell<Vec<TWire<'a, bool>>>,
    is_prover: bool,
}

impl<'a> Context<'a> {
    pub fn new<C: CircuitTrait<'a> + ?Sized>(c: &C) -> Context<'a> {
        Context {
            asserts: RefCell::new(Vec::new()),
            bugs: RefCell::new(Vec::new()),
            is_prover: c.is_prover(),
        }
    }

    pub fn finish<C: CircuitTrait<'a> + ?Sized>(
        mut self,
        c: &C,
    ) -> (Vec<TWire<'a, bool>>, Vec<TWire<'a, bool>>) {
        (self.asserts.into_inner(), self.bugs.into_inner())
    }

    /// Mark the execution as invalid if `cond` is false.  A failed assertion represents
    /// misbehavior on the part of the prover.
    pub fn assert(
        &self,
        b: &impl Builder<'a>,
        cond: TWire<'a, bool>,
        msg: impl Fn(&mut ContextEval<'a, '_>) -> String + Copy + 'a,
    ) {
        if let GateKind::Lit(..) = cond.repr.kind {
            let val = eval::LiteralEvaluator.eval_typed(b.circuit(), cond).unwrap();
            if !val {
                let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
                let mut cev = ContextEval::new(b.circuit().as_base(), &mut ev);
                eprintln!("warning: trace is trivially invalid: {}", msg(&mut cev));
            }
        } else {
            let hook = b.circuit().alloc_eval_hook_fn(move |c, ev, _w, bits| {
                let val = !bits.is_zero();
                if !val {
                    let mut cev = ContextEval::new(c, ev);
                    eprintln!("invalid trace: {}", msg(&mut cev));
                }
            });
            cond.repr.eval_hook.set(Some(hook));
        }
        self.asserts.borrow_mut().push(cond);
    }

    /// Signal an error condition of `cond` is true.  This should be used for situations like
    /// buffer overflows, which indicate a bug in the subject program.
    pub fn bug_if(
        &self,
        b: &impl Builder<'a>,
        cond: TWire<'a, bool>,
        msg: impl Fn(&mut ContextEval<'a, '_>) -> String + Copy + 'a,
    ) {
        if let GateKind::Lit(..) = cond.repr.kind {
            let val = eval::LiteralEvaluator.eval_typed(b.circuit(), cond).unwrap();
            if val {
                let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
                let mut cev = ContextEval::new(b.circuit().as_base(), &mut ev);
                eprintln!("warning: found trivial bug: {}", msg(&mut cev));
            }
        } else {
            let hook = b.circuit().alloc_eval_hook_fn(move |c, ev, _w, bits| {
                let val = !bits.is_zero();
                if val {
                    let mut cev = ContextEval::new(c, ev);
                    eprintln!("found bug: {}", msg(&mut cev));
                }
            });
            cond.repr.eval_hook.set(Some(hook));
        }
        self.bugs.borrow_mut().push(cond);
    }

    pub fn when<R, B: Builder<'a>>(
        &self,
        b: &B,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_, B>) -> R,
    ) -> R {
        f(&ContextWhen { cx: self, b, path_cond })
    }
}


pub struct ContextWhen<'a, 'b, B> {
    cx: &'b Context<'a>,
    b: &'b B,
    path_cond: TWire<'a, bool>,
}

impl<'a, 'b, B: Builder<'a>> ContextWhen<'a, 'b, B> {
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
        b: &impl Builder<'a>,
        cond: TWire<'a, bool>,
        msg: impl Fn(&mut ContextEval<'a, '_>) -> String + Copy + 'a,
    ) {
        self.cx.assert(b, self.assert_cond(cond), msg);
    }

    pub fn bug_if(
        &self,
        b: &impl Builder<'a>,
        cond: TWire<'a, bool>,
        msg: impl Fn(&mut ContextEval<'a, '_>) -> String + Copy + 'a,
    ) {
        self.cx.bug_if(b, self.bug_cond(cond), msg);
    }

    pub fn when<R, B2: Builder<'a>>(
        &self,
        b: &B2,
        path_cond: TWire<'a, bool>,
        f: impl FnOnce(&ContextWhen<'a, '_, B2>) -> R,
    ) -> R {
        self.cx.when(b, b.and(self.path_cond, path_cond), f)
    }
}


pub struct ContextEval<'a, 'b> {
    c: &'b CircuitBase<'a>,
    ev: &'b mut (dyn eval::EvaluatorObj<'a> + 'b),
}

impl<'a, 'b> ContextEval<'a, 'b> {
    pub fn new(
        c: &'b CircuitBase<'a>,
        ev: &'b mut (dyn eval::EvaluatorObj<'a> + 'b),
    ) -> ContextEval<'a, 'b> {
        ContextEval { c, ev }
    }
}

impl<'a> ContextEval<'a, '_> {
    fn eval_raw<T: FromEval<'a>>(&mut self, w: TWire<'a, T>) -> Option<T> {
        self.ev.eval_typed(self.c, w)
    }

    pub fn eval<T: FromEval<'a>>(&mut self, w: TWire<'a, T>) -> SecretValue<T> {
        SecretValue(self.eval_raw(w))
    }
}
