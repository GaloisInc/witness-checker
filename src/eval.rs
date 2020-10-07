use std::collections::HashMap;

use crate::ir::circuit::{
    Circuit, Ty, Wire, Secret, GateKind, TyKind, GadgetKindRef, UnOp, BinOp, ShiftOp, CmpOp,
};

use self::Value::Single;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value {
    Single(u64),
    Bundle(Vec<Value>),
}

impl Value {
    pub fn as_single(&self) -> Option<u64> {
        match *self {
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

    fn eval_single_wire(&mut self, w: Wire<'a>) -> Option<u64> {
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
        Some(Single(s.val?))
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

        let opt_val = eval_gate(self, w.kind);
        self.cache.insert(w, opt_val.clone());
        opt_val
    }

    fn eval_gadget(&mut self, k: GadgetKindRef<'a>, ws: &[Wire<'a>]) -> Option<Value> {
        let w = k.decompose(self.c, ws);
        self.eval_wire(w)
    }
}



fn value_mask(ty: Ty) -> Option<u64> {
    match *ty {
        TyKind::Int(sz) |
        TyKind::Uint(sz) => Some(!0 >> (64 - sz.bits())),
        TyKind::Bundle(_) => None,
    }
}

fn sign_extend(ty: Ty, val: u64) -> Option<i64> {
    let shift = match *ty {
        TyKind::Int(sz) | TyKind::Uint(sz) => 64 - sz.bits(),
        _ => return None,
    };
    Some(((val << shift) as i64) >> shift)
}

fn safe_div(x: u64, y: u64) -> u64 {
    if y == 0 { 0 } else { x / y }
}

fn safe_sdiv(x: i64, y: i64) -> i64 {
    if y == 0 { 0 } else { x / y }
}

fn safe_mod(x: u64, y: u64) -> u64 {
    if y == 0 { 0 } else { x % y }
}

fn safe_smod(x: i64, y: i64) -> i64 {
    if y == 0 { 0 } else { x % y }
}

pub fn eval_gate<'a, E: Evaluator<'a>>(e: &mut E, gk: GateKind<'a>) -> Option<Value> {
    Some(match gk {
        GateKind::Lit(x, _) => Single(x),

        GateKind::Secret(s) => return e.eval_secret(s),

        GateKind::Unary(op, a) => {
            let a_val = e.eval_single_wire(a)?;
            let ty = a.ty;
            let val = match op {
                UnOp::Not => !a_val,
                UnOp::Neg => sign_extend(ty, a_val)?.wrapping_neg() as u64,
            };
            Single(val & value_mask(ty)?)
        },

        GateKind::Binary(op, a, b) => {
            let a_val = e.eval_single_wire(a)?;
            let b_val = e.eval_single_wire(b)?;
            let ty = a.ty;
            let val = match (op, *ty) {
                (BinOp::Add, _) => a_val.wrapping_add(b_val),
                (BinOp::Sub, _) => a_val.wrapping_sub(b_val),
                (BinOp::Mul, _) => a_val.wrapping_mul(b_val),
                (BinOp::Div, TyKind::Uint(_)) => safe_div(a_val, b_val),
                (BinOp::Div, TyKind::Int(_)) =>
                    safe_sdiv(sign_extend(ty, a_val)?, sign_extend(ty, b_val)?) as u64,
                (BinOp::Div, _) => return None,
                (BinOp::Mod, TyKind::Uint(_)) => safe_mod(a_val, b_val),
                (BinOp::Mod, TyKind::Int(_)) =>
                    safe_smod(sign_extend(ty, a_val)?, sign_extend(ty, b_val)?) as u64,
                (BinOp::Mod, _) => return None,
                (BinOp::And, _) => a_val & b_val,
                (BinOp::Or, _) => a_val | b_val,
                (BinOp::Xor, _) => a_val ^ b_val,
            };
            Single(val & value_mask(ty)?)
        },

        GateKind::Shift(op, a, b) => {
            let a_val = e.eval_single_wire(a)?;
            let b_val = e.eval_single_wire(b)?;
            let ty = a.ty;
            let val = match (op, *ty) {
                (ShiftOp::Shl, _) => a_val << b_val,
                (ShiftOp::Shr, TyKind::Uint(_)) => a_val >> b_val,
                (ShiftOp::Shr, TyKind::Int(_)) =>
                    (sign_extend(ty, a_val)? >> b_val) as u64,
                (ShiftOp::Shr, _) => return None,
            };
            Single(val & value_mask(ty)?)
        },

        GateKind::Compare(op, a, b) => {
            let a_val = e.eval_single_wire(a)?;
            let b_val = e.eval_single_wire(b)?;
            let ty = a.ty;
            let val: bool = match (op, *ty) {
                (CmpOp::Eq, _) => (a_val & value_mask(ty)?) == (b_val & value_mask(ty)?),
                (CmpOp::Ne, _) => (a_val & value_mask(ty)?) != (b_val & value_mask(ty)?),
                (CmpOp::Lt, TyKind::Int(_)) => sign_extend(ty, a_val)? < sign_extend(ty, b_val)?,
                (CmpOp::Lt, _) => a_val < b_val,
                (CmpOp::Le, TyKind::Int(_)) => sign_extend(ty, a_val)? <= sign_extend(ty, b_val)?,
                (CmpOp::Le, _) => a_val <= b_val,
                (CmpOp::Gt, TyKind::Int(_)) => sign_extend(ty, a_val)? > sign_extend(ty, b_val)?,
                (CmpOp::Gt, _) => a_val > b_val,
                (CmpOp::Ge, TyKind::Int(_)) => sign_extend(ty, a_val)? >= sign_extend(ty, b_val)?,
                (CmpOp::Ge, _) => a_val >= b_val,
            };
            Single(val as u64)
        },

        GateKind::Mux(c, x, y) => {
            let c_val = e.eval_single_wire(c)?;
            // Avoid evaluating inputs that don't contribute to the output.
            if c_val != 0 { e.eval_wire(x)? } else { e.eval_wire(y)? }
        },

        GateKind::Cast(a, new_ty) => {
            let a_val = e.eval_single_wire(a)?;
            let val = match *a.ty {
                TyKind::Int(_) => sign_extend(a.ty, a_val)? as u64,
                _ => a_val,
            };
            Single(val & value_mask(new_ty)?)
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
