use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter;
use num_bigint::{BigUint, BigInt, Sign};
use num_traits::{Signed, Zero};

use crate::ir::circuit::{
    self, Circuit, Ty, Wire, Secret, Bits, GateKind, TyKind, GadgetKindRef, UnOp, BinOp, ShiftOp,
    CmpOp,
};

use self::Value::Single;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value {
    /// The value of an integer-typed wire, in arbitrary precision.  For `Uint` wires, this is in
    /// the range `0 .. 2^N`; for `Int`, it's in the range `-2^(N-1) .. 2^(N-1)`.
    Single(BigInt),
    Bundle(Vec<Value>),
}

impl Value {
    pub fn from_lit(ty: Ty, bits: Bits) -> Value {
        Value::Single(bits.to_bigint(ty))
    }

    /// Truncate an arbitrary-precision value `i` to the appropriate range for `ty`.
    pub fn trunc(ty: Ty, i: BigInt) -> Value {
        match *ty {
            TyKind::Uint(sz) => {
                let i = if i.is_negative() || i.bits() > sz.bits() as u64 {
                    let mask = (BigInt::from(1) << sz.bits()) - 1;
                    i & mask
                } else {
                    i
                };
                Single(i)
            },
            TyKind::Int(sz) => {
                let out_of_range =
                    (i.is_positive() && i.bits() > sz.bits() as u64) ||
                        (i.is_negative() && i.bits() >= sz.bits() as u64);
                let i = if out_of_range {
                    let mask = (BigInt::from(1) << sz.bits()) - 1;
                    let step = BigInt::from(1) << (sz.bits() - 1);
                    ((i + &step) & mask) - &step
                } else {
                    i
                };
                Single(i)
            },
            _ => panic!("can't construct a Bundle from a single integer"),
        }
    }

    pub fn as_single(&self) -> Option<&BigInt> {
        match *self {
            Value::Single(ref x) => Some(x),
            _ => None,
        }
    }

    pub fn unwrap_single(self) -> Option<BigInt> {
        match self {
            Value::Single(x) => Some(x),
            _ => None,
        }
    }

    pub fn as_bundle(&self) -> Option<&[Value]> {
        match *self {
            Value::Bundle(ref vals) => Some(vals),
            _ => None,
        }
    }
}

pub trait Evaluator<'a>: SecretEvaluator<'a> {
    fn eval_wire(&mut self, w: Wire<'a>) -> Option<Value>;

    fn eval_gadget(&mut self, k: GadgetKindRef<'a>, ws: &[Wire<'a>]) -> Option<Value>;

    fn eval_single_wire(&mut self, w: Wire<'a>) -> Option<BigInt> {
        match self.eval_wire(w) {
            Some(Single(x)) => Some(x),
            _ => None,
        }
    }
}

pub trait SecretEvaluator<'a> {
    fn eval_secret(&mut self, s: Secret<'a>) -> Option<Value>;
}


/// Public evaluation mode.  Secret values are always ignored, even when they are available.
#[derive(Clone, Copy, Debug, Default)]
pub struct Public;
impl<'a> SecretEvaluator<'a> for Public {
    fn eval_secret(&mut self, _s: Secret<'a>) -> Option<Value> { None }
}

/// Secret evaluation mode.  Secret values will be used if they are available in the circuit.
#[derive(Clone, Copy, Debug, Default)]
pub struct RevealSecrets;
impl<'a> SecretEvaluator<'a> for RevealSecrets {
    fn eval_secret(&mut self, s: Secret<'a>) -> Option<Value> {
        Some(Value::from_lit(s.ty, s.val?))
    }
}


/// Evaluator that caches the result of each wire.  This avoids duplicate work in cases with
/// sharing.
pub struct CachingEvaluator<'a, 'c, S> {
    c: &'c Circuit<'a>,
    cache: HashMap<Wire<'a>, Option<Value>>,
    secret_eval: S,
}
impl<'a, 'c, S: Default> CachingEvaluator<'a, 'c, S> {
    pub fn new(c: &'c Circuit<'a>) -> Self {
        CachingEvaluator {
            c,
            cache: HashMap::new(),
            secret_eval: S::default(),
        }
    }
}


impl<'a, 'c, S: SecretEvaluator<'a>> SecretEvaluator<'a> for CachingEvaluator<'a, 'c, S> {
    fn eval_secret(&mut self, s: Secret<'a>) -> Option<Value> {
        self.secret_eval.eval_secret(s)
    }
}

impl<'a, 'c, S: SecretEvaluator<'a>> Evaluator<'a> for CachingEvaluator<'a, 'c, S> {
    fn eval_wire(&mut self, w: Wire<'a>) -> Option<Value> {
        if let Some(opt_val) = self.cache.get(&w) {
            return opt_val.clone();
        }

        let order = circuit::walk_wires_filtered(
            iter::once(w),
            |w| !self.cache.contains_key(&w),
        ).collect::<Vec<_>>();
        for w in order {
            let opt_val = eval_gate(self, w.kind);
            self.cache.insert(w, opt_val.clone());
        }
        self.cache.get(&w).unwrap().clone()
    }

    fn eval_gadget(&mut self, k: GadgetKindRef<'a>, ws: &[Wire<'a>]) -> Option<Value> {
        let w = k.decompose(self.c, ws);
        self.eval_wire(w)
    }
}



fn safe_div(x: BigInt, y: BigInt) -> BigInt {
    if y.is_zero() { 0.into() } else { x / y }
}

fn safe_mod(x: BigInt, y: BigInt) -> BigInt {
    if y.is_zero() { 0.into() } else { x % y }
}

pub fn eval_gate<'a, E: Evaluator<'a>>(e: &mut E, gk: GateKind<'a>) -> Option<Value> {
    Some(match gk {
        GateKind::Lit(bits, ty) => Value::from_lit(ty, bits),

        GateKind::Secret(s) => return e.eval_secret(s),

        GateKind::Unary(op, a) => {
            let a_val = e.eval_single_wire(a)?;
            let ty = a.ty;
            let val = match op {
                UnOp::Not => !a_val,
                UnOp::Neg => -a_val,
            };
            Value::trunc(ty, val)
        },

        GateKind::Binary(op, a, b) => {
            let a_val = e.eval_single_wire(a)?;
            let b_val = e.eval_single_wire(b)?;
            let ty = a.ty;
            let val = match op {
                BinOp::Add => a_val + b_val,
                BinOp::Sub => a_val - b_val,
                BinOp::Mul => a_val * b_val,
                BinOp::Div => safe_div(a_val, b_val),
                BinOp::Mod => safe_mod(a_val, b_val),
                BinOp::And => a_val & b_val,
                BinOp::Or => a_val | b_val,
                BinOp::Xor => a_val ^ b_val,
            };
            Value::trunc(ty, val)
        },

        GateKind::Shift(op, a, b) => {
            let a_val = e.eval_single_wire(a)?;
            let b_val = e.eval_single_wire(b)?;
            let b_val = u16::try_from(b_val).ok()?;
            let ty = a.ty;
            let val = match op {
                ShiftOp::Shl => a_val << b_val,
                ShiftOp::Shr => a_val >> b_val,
            };
            Value::trunc(ty, val)
        },

        GateKind::Compare(op, a, b) => {
            let a_val = e.eval_single_wire(a)?;
            let b_val = e.eval_single_wire(b)?;
            let ty = a.ty;
            let val: bool = match op {
                CmpOp::Eq => a_val == b_val,
                CmpOp::Ne => a_val != b_val,
                CmpOp::Lt => a_val < b_val,
                CmpOp::Le => a_val <= b_val,
                CmpOp::Gt => a_val > b_val,
                CmpOp::Ge => a_val >= b_val,
            };
            Value::trunc(ty, BigInt::from(val as u8))
        },

        GateKind::Mux(c, x, y) => {
            let c_val = e.eval_single_wire(c)?;
            // Avoid evaluating inputs that don't contribute to the output.
            if !c_val.is_zero() { e.eval_wire(x)? } else { e.eval_wire(y)? }
        },

        GateKind::Cast(a, new_ty) => {
            let a_val = e.eval_single_wire(a)?;
            Value::trunc(new_ty, a_val)
        },

        GateKind::Pack(ws) => {
            let vals = ws.iter().map(|&w| e.eval_wire(w)).collect::<Option<Vec<_>>>()?;
            Value::Bundle(vals)
        },

        GateKind::Extract(w, i) => {
            let val = e.eval_wire(w)?;
            match val {
                Value::Single(_) => return None,
                Value::Bundle(ref vals) => vals.get(i)?.clone(),
            }
        },

        GateKind::Gadget(k, ws) => {
            e.eval_gadget(k, ws)?
        },
    })
}
