use std::convert::TryFrom;
use std::iter;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use crate::ir::migrate::{self, Migrate};

use crate::ir::circuit::{
    self, CircuitBase, CircuitTrait, Ty, Wire, Secret, Bits, AsBits, GateKind, TyKind, UnOp, BinOp,
    ShiftOp, CmpOp, GateValue,
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

    fn eval_single_wire(&mut self, w: Wire<'a>) -> Result<BigInt, Error<'a>> {
        match self.eval_wire(w)? {
            Single(x) => Ok(x),
            _ => Err(Error::Other),
        }
    }
}

pub trait SecretEvaluator<'a> {
    const REVEAL_SECRETS: bool;
}


/// Public evaluation mode.  Secret values are always ignored, even when they are available.
#[derive(Clone, Copy, Debug, Default, Migrate)]
pub struct Public;
impl<'a> SecretEvaluator<'a> for Public {
    const REVEAL_SECRETS: bool = false;
}

/// Secret evaluation mode.  Secret values will be used if they are available in the circuit.
#[derive(Clone, Copy, Debug, Default, Migrate)]
pub struct RevealSecrets;
impl<'a> SecretEvaluator<'a> for RevealSecrets {
    const REVEAL_SECRETS: bool = true;
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
    /// Evaluation failed because some input was unevaluated.
    UnevalInput,
    /// Evaluation failed for some other reason.  This is considered a permanent failure (the cache
    /// entry is never invalidated).
    Other,
}

impl<'a> From<&'_ Error<'a>> for Error<'a> {
    fn from(x: &Error<'a>) -> Error<'a> { x.clone() }
}

impl<'a, S: Default> CachingEvaluator<'a, S> {
    pub fn new<C: CircuitTrait<'a> + ?Sized>(circuit: &'a C) -> Self {
        CachingEvaluator {
            secret_eval: S::default(),
            circuit: circuit.as_base(),
        }
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
    const REVEAL_SECRETS: bool = S::REVEAL_SECRETS;
}

impl<'a, S: SecretEvaluator<'a>> Evaluator<'a> for CachingEvaluator<'a, S> {
    fn eval_wire(&mut self, w: Wire<'a>) -> EvalResult<'a> {
        let (bits, sec) = eval_wire(self.circuit, w)?;
        if sec && !S::REVEAL_SECRETS {
            return Err(Error::Other);
        }
        Ok(Value::from_bits(w.ty, bits))
    }
}


pub struct LiteralEvaluator;

impl<'a> SecretEvaluator<'a> for LiteralEvaluator {
    const REVEAL_SECRETS: bool = false;
}

impl<'a> Evaluator<'a> for LiteralEvaluator {
    fn eval_wire(&mut self, w: Wire<'a>) -> EvalResult<'a> {
        match w.kind {
            GateKind::Lit(bits, ty) => Ok(Value::from_bits(ty, bits)),
            _ => Err(Error::Other),
        }
    }
}


fn convert_gate_value<'a>(gv: GateValue<'a>) -> Result<(Bits<'a>, bool), Error<'a>> {
    match gv {
        GateValue::Unset => Err(Error::UnevalInput),
        GateValue::Public(bits) => Ok((bits, false)),
        GateValue::Secret(bits) => Ok((bits, true)),
        GateValue::NeedsSecret(s) => Err(Error::UnknownSecret(s)),
        GateValue::Failed => Err(Error::Other),
    }
}

/// Get the value of `w` as `Bits` and a flag indicating whether the value is derived from secrets.
fn get_value<'a>(w: Wire<'a>) -> Result<(Bits<'a>, bool), Error<'a>> {
    convert_gate_value(w.value.get())
}

fn get_int_value<'a>(w: Wire<'a>) -> Result<(BigInt, bool), Error<'a>> {
    let (bits, sec) = get_value(w)?;
    Ok((bits.to_bigint(w.ty), sec))
}

fn trunc<'a, T: AsBits>(c: &CircuitBase<'a>, ty: Ty<'a>, x: T) -> Bits<'a> {
    x.as_bits(c, ty.integer_size())
}

fn safe_div(x: BigInt, y: BigInt) -> BigInt {
    if y.is_zero() { 0.into() } else { x / y }
}

fn safe_mod(x: BigInt, y: BigInt) -> BigInt {
    if y.is_zero() { 0.into() } else { x % y }
}

pub fn eval_gate<'a>(
    c: &CircuitBase<'a>,
    ty: Ty<'a>,
    gk: GateKind<'a>,
) -> Result<(Bits<'a>, bool), Error<'a>> {
    Ok(match gk {
        GateKind::Lit(bits, _) => (bits, false),

        GateKind::Secret(s) => match s.try_val() {
            Some(bits) => (bits, true),
            None => return Err(Error::UnknownSecret(s)),
        },

        GateKind::Erased(e) => convert_gate_value(e.gate_value())?,

        GateKind::Unary(op, a) => {
            let (a_val, a_sec) = get_int_value(a)?;
            let val = match op {
                UnOp::Not => !a_val,
                UnOp::Neg => -a_val,
            };
            (trunc(c, ty, val), a_sec)
        },

        GateKind::Binary(op, a, b) => {
            let (a_val, a_sec) = get_int_value(a)?;
            let (b_val, b_sec) = get_int_value(b)?;
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
            (trunc(c, ty, val), a_sec || b_sec)
        },

        GateKind::Shift(op, a, b) => {
            let (a_val, a_sec) = get_int_value(a)?;
            let (b_val, b_sec) = get_int_value(b)?;
            let b_val = u16::try_from(b_val).map_err(|_| Error::Other)?;
            let val = match op {
                ShiftOp::Shl => a_val << b_val,
                ShiftOp::Shr => a_val >> b_val,
            };
            (trunc(c, ty, val), a_sec || b_sec)
        },

        GateKind::Compare(op, a, b) => {
            let (a_val, a_sec) = get_int_value(a)?;
            let (b_val, b_sec) = get_int_value(b)?;
            let val: bool = match op {
                CmpOp::Eq => a_val == b_val,
                CmpOp::Ne => a_val != b_val,
                CmpOp::Lt => a_val < b_val,
                CmpOp::Le => a_val <= b_val,
                CmpOp::Gt => a_val > b_val,
                CmpOp::Ge => a_val >= b_val,
            };
            (trunc(c, ty, val), a_sec || b_sec)
        },

        GateKind::Mux(c, x, y) => {
            let (c_val, c_sec) = get_int_value(c)?;
            // Secrecy: If the condition is public, then the result is only as secret as the chosen
            // input (`x` or `y`).  If the condition is secret, then the result is always secret.
            if !c_val.is_zero() {
                let (x_bits, x_sec) = get_value(x)?;
                (x_bits, x_sec || c_sec)
            } else {
                let (y_bits, y_sec) = get_value(y)?;
                (y_bits, y_sec || c_sec)
            }
        },

        GateKind::Cast(a, _) => {
            let (a_val, a_sec) = get_int_value(a)?;
            (trunc(c, ty, a_val), a_sec)
        },

        GateKind::Pack(ws) => {
            let mut digits = Vec::with_capacity(ty.digits());
            let mut sec = false;
            for &w in ws {
                let (w_bits, w_sec) = get_value(w)?;
                digits.extend_from_slice(w_bits.0);
                sec |= w_sec;
            }
            let bits = c.intern_bits(&digits);
            (bits, sec)
        },

        GateKind::Extract(w, i) => {
            let (w_bits, w_sec) = get_value(w)?;
            let tys = match *w.ty {
                TyKind::Bundle(tys) => tys,
                _ => panic!("expected Extract input to have Bundle type"),
            };
            let pos = tys[..i].iter().map(|ty| ty.digits()).sum();
            let len = tys[i].digits();
            let bits = c.intern_bits(&w_bits.0[pos .. pos + len]);
            (bits, w_sec)
        },

        GateKind::Gadget(k, ws) => {
            let mut tys = Vec::with_capacity(ws.len());
            let mut vals = Vec::with_capacity(ws.len());
            let mut sec = false;
            for &w in ws {
                tys.push(w.ty);
                match get_value(w) {
                    Ok((w_bits, w_sec)) => {
                        vals.push(Ok(Value::from_bits(w.ty, w_bits)));
                        sec |= w_sec;
                    },
                    Err(e) => {
                        vals.push(Err(e));
                    },
                }
            }

            let v = k.eval(&tys, &vals)?;
            let bits = v.to_bits(c, ty);
            (bits, sec)
        },
    })
}

pub fn eval_gate_public<'a, C>(c: &C, ty: Ty<'a>, gk: GateKind<'a>) -> Option<Value>
where C: CircuitTrait<'a> + ?Sized {
    let (bits, sec) = eval_gate(c.as_base(), ty, gk).ok()?;
    if sec {
        return None;
    }
    Some(Value::from_bits(ty, bits))
}

pub fn eval_gate_secret<'a, C>(c: &C, ty: Ty<'a>, gk: GateKind<'a>) -> Option<Value>
where C: CircuitTrait<'a> + ?Sized {
    let (bits, _sec) = eval_gate(c.as_base(), ty, gk).ok()?;
    Some(Value::from_bits(ty, bits))
}

pub fn eval_wire<'a, C: CircuitTrait<'a> + ?Sized>(
    c: &C,
    w: Wire<'a>,
) -> Result<(Bits<'a>, bool), Error<'a>> {
    if w.value.is_valid() {
        return get_value(w);
    }

    let order = circuit::walk_wires_filtered(
        iter::once(w),
        |w| !w.value.is_valid(),
    ).collect::<Vec<_>>();
    for w in order {
        let result = eval_gate(c.as_base(), w.ty, w.kind);
        w.value.set(match result {
            Ok((bits, false)) => GateValue::Public(bits),
            Ok((bits, true)) => GateValue::Secret(bits),
            Err(Error::UnknownSecret(s)) => GateValue::NeedsSecret(s),
            Err(Error::UnevalInput) => GateValue::Unset,
            Err(Error::Other) => GateValue::Failed,
        });
    }

    get_value(w)
}

pub fn eval_wire_public<'a, C: CircuitTrait<'a> + ?Sized>(c: &C, w: Wire<'a>) -> Option<Value> {
    eval_gate_public(c, w.ty, w.kind)
}

pub fn eval_wire_secret<'a, C: CircuitTrait<'a> + ?Sized>(c: &C, w: Wire<'a>) -> Option<Value> {
    eval_gate_secret(c, w.ty, w.kind)
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
