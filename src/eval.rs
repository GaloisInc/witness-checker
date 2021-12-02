use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter;
use std::marker::PhantomData;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use crate::ir::migrate::{self, Migrate};

use crate::ir::circuit::{
    self, CircuitBase, CircuitTrait, Ty, Wire, Secret, Erased, Bits, AsBits, GateKind, TyKind,
    GadgetKindRef, UnOp, BinOp, ShiftOp, CmpOp, GateValue,
};

use self::Value::Single;

#[derive(Clone, PartialEq, Eq, Debug, Migrate)]
pub enum Value {
    /// The value of an integer-typed wire, in arbitrary precision.  For `Uint` wires, this is in
    /// the range `0 .. 2^N`; for `Int`, it's in the range `-2^(N-1) .. 2^(N-1)`.
    Single(BigInt),
    Bundle(Vec<Value>),
}

impl Value {
    pub fn from_bits(ty: Ty, bits: Bits) -> Value {
        match *ty {
            TyKind::Int(_) |
            TyKind::Uint(_) => {
                Value::Single(bits.to_bigint(ty))
            },
            TyKind::Bundle(tys) => {
                let mut vals = Vec::with_capacity(tys.len());
                let mut pos = 0;
                for &ty in tys {
                    let end = pos + ty.digits();
                    let field_bits = Bits(&bits.0[pos .. end]);
                    vals.push(Value::from_bits(ty, field_bits));
                    pos = end;
                }
                assert_eq!(pos, bits.0.len());
                Value::Bundle(vals)
            },
        }
    }

    pub fn to_bits<'a>(&self, c: &CircuitBase<'a>, ty: Ty<'a>) -> Bits<'a> {
        match (self, *ty) {
            (&Value::Single(ref v), TyKind::Int(sz)) |
            (&Value::Single(ref v), TyKind::Uint(sz)) => {
                v.as_bits(c, sz)
            },
            (&Value::Bundle(ref vs), TyKind::Bundle(tys)) => {
                assert_eq!(vs.len(), tys.len());
                let mut digits = Vec::with_capacity(ty.digits());
                for (v, &ty) in vs.iter().zip(tys.iter()) {
                    let bits = v.to_bits(c, ty);
                    digits.extend_from_slice(&bits.0);
                }
                c.intern_bits(&digits)
            },
            _ => panic!("value {:?} doesn't match type {:?}", self, ty),
        }
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
                    (i.is_positive() && i.bits() >= sz.bits() as u64) ||
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
    fn eval_wire(&mut self, w: Wire<'a>) -> EvalResult<'a>;

    fn eval_gadget(&mut self, k: GadgetKindRef<'a>, ws: &[Wire<'a>]) -> EvalResult<'a>;

    fn eval_single_wire(&mut self, w: Wire<'a>) -> Result<BigInt, Error<'a>> {
        match self.eval_wire(w)? {
            Single(x) => Ok(x),
            _ => Err(Error::Other),
        }
    }
}

pub trait SecretEvaluator<'a> {
    fn eval_secret(&mut self, s: Secret<'a>) -> EvalResult<'a>;
    fn eval_erased(&mut self, e: Erased<'a>) -> EvalResult<'a>;
}


/// Public evaluation mode.  Secret values are always ignored, even when they are available.
#[derive(Clone, Copy, Debug, Default, Migrate)]
pub struct Public;
impl<'a> SecretEvaluator<'a> for Public {
    fn eval_secret(&mut self, s: Secret<'a>) -> EvalResult<'a> { Err(Error::UnknownSecret(s)) }
    fn eval_erased(&mut self, _e: Erased<'a>) -> EvalResult<'a> { Err(Error::Other) }
}

/// Secret evaluation mode.  Secret values will be used if they are available in the circuit.
#[derive(Clone, Copy, Debug, Default, Migrate)]
pub struct RevealSecrets;
impl<'a> SecretEvaluator<'a> for RevealSecrets {
    fn eval_secret(&mut self, s: Secret<'a>) -> EvalResult<'a> {
        let val = match s.try_val() {
            Some(x) => x,
            None => return Err(Error::UnknownSecret(s)),
        };
        Ok(Value::from_bits(s.ty, val))
    }

    fn eval_erased(&mut self, e: Erased<'a>) -> EvalResult<'a> {
        e.secret_value.clone().ok_or(Error::Other)
    }
}


/// Evaluator that caches the result of each wire.  This avoids duplicate work in cases with
/// sharing.
pub struct CachingEvaluator<'a, S> {
    secret_eval: S,
    circuit: &'a CircuitBase<'a>,
}

/// Result of evaluating a `Wire`.  Evaluation produces a `Value` on success.  It fails if the
/// `Wire` depends on a `Secret` whose value is unknown or not yet set, in which case it returns
/// the relevant `Secret`.
pub type EvalResult<'a> = Result<Value, Error<'a>>;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Migrate)]
pub enum Error<'a> {
    /// Evaluation failed because the value of this secret was unknown at the time.
    UnknownSecret(Secret<'a>),
    /// Evaluation failed for some other reason.  This is considered a permanent failure (the cache
    /// entry is never invalidated).
    Other,
}

impl<'a> From<&'_ Error<'a>> for Error<'a> {
    fn from(x: &Error<'a>) -> Error<'a> { x.clone() }
}

impl<'a> Error<'a> {
    fn is_valid(&self) -> bool {
        match *self {
            Error::UnknownSecret(s) => !s.has_val(),
            Error::Other => true,
        }
    }
}

impl<'a, S: Default> CachingEvaluator<'a, S> {
    pub fn new<C: CircuitTrait<'a> + ?Sized>(circuit: &'a C) -> Self {
        CachingEvaluator {
            secret_eval: S::default(),
            circuit: circuit.as_base(),
        }
    }
}

impl<'a, S> CachingEvaluator<'a, S> {
    fn has_valid_entry(&self, w: Wire<'a>) -> bool {
        w.value.is_valid()
    }
}

impl<'a, 'b, S: Migrate<'a, 'b>> Migrate<'a, 'b> for CachingEvaluator<'a, S> {
    type Output = CachingEvaluator<'b, S::Output>;

    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(
        self,
        v: &mut V,
    ) -> CachingEvaluator<'b, S::Output> {
        CachingEvaluator {
            secret_eval: v.visit(self.secret_eval),
            circuit: v.new_circuit(),
        }
    }
}

impl<'a, S: SecretEvaluator<'a>> SecretEvaluator<'a> for CachingEvaluator<'a, S> {
    fn eval_secret(&mut self, s: Secret<'a>) -> EvalResult<'a> {
        self.secret_eval.eval_secret(s)
    }

    fn eval_erased(&mut self, e: Erased<'a>) -> EvalResult<'a> {
        self.secret_eval.eval_erased(e)
    }
}

impl<'a, S: SecretEvaluator<'a>> Evaluator<'a> for CachingEvaluator<'a, S> {
    fn eval_wire(&mut self, w: Wire<'a>) -> EvalResult<'a> {
        match w.value.get() {
            GateValue::Unset => {},
            GateValue::Public(bits) |
            GateValue::Secret(bits) => return Ok(Value::from_bits(w.ty, bits)),
            GateValue::NeedsSecret(s) => return Err(Error::UnknownSecret(s)),
            GateValue::Failed => return Err(Error::Other),
        }

        let order = circuit::walk_wires_filtered(
            iter::once(w),
            |w| !self.has_valid_entry(w),
        ).collect::<Vec<_>>();
        for w in order {
            let result = eval_gate(self, w.kind);
            w.value.set(match result {
                Ok(v) => GateValue::Secret(v.to_bits(self.circuit, w.ty)),
                Err(Error::UnknownSecret(s)) => GateValue::NeedsSecret(s),
                Err(Error::Other) => GateValue::Failed,
            });
        }
        match w.value.get() {
            GateValue::Unset => unreachable!(),
            GateValue::Public(bits) |
            GateValue::Secret(bits) => return Ok(Value::from_bits(w.ty, bits)),
            GateValue::NeedsSecret(s) => return Err(Error::UnknownSecret(s)),
            GateValue::Failed => return Err(Error::Other),
        }
    }

    fn eval_gadget(&mut self, k: GadgetKindRef<'a>, ws: &[Wire<'a>]) -> EvalResult<'a> {
        let tys = ws.iter().map(|w| w.ty).collect::<Vec<_>>();
        let vals = ws.iter().map(|&w| self.eval_wire(w)).collect::<Vec<_>>();
        k.eval(&tys, &vals)
    }
}


pub struct LiteralEvaluator;

impl<'a> SecretEvaluator<'a> for LiteralEvaluator {
    fn eval_secret(&mut self, s: Secret<'a>) -> EvalResult<'a> {
        Err(Error::UnknownSecret(s))
    }

    fn eval_erased(&mut self, _e: Erased<'a>) -> EvalResult<'a> {
        Err(Error::Other)
    }
}

impl<'a> Evaluator<'a> for LiteralEvaluator {
    fn eval_wire(&mut self, w: Wire<'a>) -> EvalResult<'a> {
        match w.kind {
            GateKind::Lit(bits, ty) => Ok(Value::from_bits(ty, bits)),
            _ => Err(Error::Other),
        }
    }

    fn eval_gadget(&mut self, k: GadgetKindRef<'a>, ws: &[Wire<'a>]) -> EvalResult<'a> {
        let tys = ws.iter().map(|w| w.ty).collect::<Vec<_>>();
        let vals = ws.iter().map(|&w| self.eval_wire(w)).collect::<Vec<_>>();
        k.eval(&tys, &vals)
    }
}


fn safe_div(x: BigInt, y: BigInt) -> BigInt {
    if y.is_zero() { 0.into() } else { x / y }
}

fn safe_mod(x: BigInt, y: BigInt) -> BigInt {
    if y.is_zero() { 0.into() } else { x % y }
}

pub fn eval_gate<'a, E: Evaluator<'a>>(e: &mut E, gk: GateKind<'a>) -> EvalResult<'a> {
    Ok(match gk {
        GateKind::Lit(bits, ty) => Value::from_bits(ty, bits),

        GateKind::Secret(s) => return e.eval_secret(s),

        GateKind::Erased(erased) => return e.eval_erased(erased),

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
            let b_val = u16::try_from(b_val).map_err(|_| Error::Other)?;
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
            let vals = ws.iter().map(|&w| e.eval_wire(w)).collect::<Result<Vec<_>, _>>()?;
            Value::Bundle(vals)
        },

        GateKind::Extract(w, i) => {
            let val = e.eval_wire(w)?;
            match val {
                Value::Single(_) => return Err(Error::Other),
                Value::Bundle(ref vals) => vals.get(i).ok_or(Error::Other)?.clone(),
            }
        },

        GateKind::Gadget(k, ws) => {
            e.eval_gadget(k, ws)?
        },
    })
}


#[cfg(test)]
mod test {
    use crate::ir::circuit::{Arenas, CircuitBase, CircuitExt};
    use super::*;

    #[test]
    fn value_trunc_uint_to_int() {
        let arenas = Arenas::new();
        let c = CircuitBase::new(&arenas, true);
        let ty_i8 = c.ty(TyKind::I8);

        for &x in [0_u8, 1, 126, 127, 128, 129, 254, 255].iter() {
            let i = BigInt::from(x);
            let j = Value::trunc(ty_i8, i).unwrap_single().unwrap();
            assert_eq!(j, BigInt::from(x as i8));
        }
    }
}
