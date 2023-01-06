use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use scuttlebutt::field::{FiniteField, Gf40, Gf45, F56b, F63b, F64b};
use crate::ir::migrate::{self, Migrate};

use crate::ir::circuit::{
    self, CircuitBase, CircuitTrait, Field, FromBits, Ty, Wire, Secret, Bits, AsBits, GateKind, TyKind, UnOp, BinOp,
    ShiftOp, CmpOp, GateValue, Function, SecretValue, SecretInputId,
};

use self::Value::SingleField;
use self::Value::SingleInteger;

#[derive(Clone, PartialEq, Eq, Debug, Migrate)]
pub enum Value {
    /// The value of an integer-typed wire, in arbitrary precision.  For `Uint` wires, this is in
    /// the range `0 .. 2^N`; for `Int`, it's in the range `-2^(N-1) .. 2^(N-1)`.
    SingleInteger(BigInt),
    SingleField(Vec<u32>),
    Bundle(Vec<Value>),
}

impl Value {
    pub fn from_bits(ty: Ty, bits: Bits) -> Value {
        match *ty {
            TyKind::Int(_) |
            TyKind::Uint(_) => {
                Value::SingleInteger(bits.to_bigint(ty))
            },
            TyKind::GF(_) => {
                Value::SingleField(bits.0.into())
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
            (&Value::SingleInteger(ref v), TyKind::Int(sz)) |
            (&Value::SingleInteger(ref v), TyKind::Uint(sz)) => {
                v.as_bits(c, sz)
            },
            (&Value::SingleField(ref v), TyKind::GF(field)) => {
                c.intern_bits(v)
            }
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
                SingleInteger(i)
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
                SingleInteger(i)
            },
            _ => panic!("can't construct a Bundle from a single integer"),
        }
    }

    pub fn as_single(&self) -> Option<&BigInt> {
        match *self {
            Value::SingleInteger(ref x) => Some(x),
            _ => None,
        }
    }

    pub fn unwrap_single(self) -> Option<BigInt> {
        match self {
            Value::SingleInteger(x) => Some(x),
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

    fn eval_single_integer_wire(&mut self, w: Wire<'a>) -> Result<BigInt, Error<'a>> {
        match self.eval_wire(w)? {
            SingleInteger(x) => Ok(x),
            _ => Err(Error::Other),
        }
    }

    fn eval_single_field_wire(&mut self, w: Wire<'a>) -> Result<Vec<u32>, Error<'a>> {
        match self.eval_wire(w)? {
            SingleField(x) => Ok(x),
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

fn get_int_value<'a>(
    ecx: &impl EvalContext<'a>,
    w: Wire<'a>,
) -> Result<(BigInt, bool), Error<'a>> {
    let (bits, sec) = ecx.get_value(w)?;
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

trait EvalContext<'a> {
    /// Get the value of `w` as `Bits` and a flag indicating whether the value is derived from
    /// secrets.
    fn get_value(&self, w: Wire<'a>) -> Result<(Bits<'a>, bool), Error<'a>>;
    fn eval_secret(&self, s: Secret<'a>) -> Result<Bits<'a>, Error<'a>>;
    fn eval_argument(&self, i: usize) -> Result<(Bits<'a>, bool), Error<'a>>;
}

struct TopLevelContext;
impl<'a> EvalContext<'a> for TopLevelContext {
    fn get_value(&self, w: Wire<'a>) -> Result<(Bits<'a>, bool), Error<'a>> {
        convert_gate_value(w.value.get())
    }

    fn eval_secret(&self, s: Secret<'a>) -> Result<Bits<'a>, Error<'a>> {
        match s.secret_value() {
            SecretValue::ProverInit(b) => Ok(b),
            SecretValue::ProverUninit => Err(Error::UnknownSecret(s)),
            SecretValue::VerifierUnknown =>  Err(Error::UnknownSecret(s)),
            SecretValue::FunctionInput(_) => unreachable!("found FunctionInput at top level?"),
        }
    }

    fn eval_argument(&self, _i: usize) -> Result<(Bits<'a>, bool), Error<'a>> {
        panic!("can't access arguments at top level")
    }
}

struct FunctionContext<'a> {
    args: Vec<(Bits<'a>, bool)>,
    /// The value of each secret used by this function.  `None` means the value is not known at
    /// this time.
    secrets: Vec<Option<Bits<'a>>>,
    cache: HashMap<Wire<'a>, (Bits<'a>, bool)>,
}

impl<'a> EvalContext<'a> for FunctionContext<'a> {
    fn get_value(&self, w: Wire<'a>) -> Result<(Bits<'a>, bool), Error<'a>> {
        self.cache.get(&w).cloned().ok_or(Error::UnevalInput)
    }

    fn eval_secret(&self, s: Secret<'a>) -> Result<Bits<'a>, Error<'a>> {
        match s.secret_value() {
            SecretValue::FunctionInput(id) => {
                self.secrets[id.0].ok_or(Error::UnknownSecret(s))
            },
            v => unreachable!("found non-FunctionInput ({:?}) inside a function?", v),
        }
    }

    fn eval_argument(&self, i: usize) -> Result<(Bits<'a>, bool), Error<'a>> {
        Ok(self.args[i])
    }
}

pub fn eval_unop_integer<'a>(
    c: &CircuitBase<'a>,
    op: UnOp,
    a_bits: Bits<'a>,
    ty: Ty<'a>,
) -> Bits<'a> {
    let a_val = a_bits.to_bigint(ty);
    let val = match op {
        UnOp::Not => !a_val,
        UnOp::Neg => -a_val,
    };
    trunc(c, ty, val)
}


pub fn eval_unop_galois_field<'a>(
    c: &CircuitBase<'a>,
    op: UnOp,
    a_bits: Bits<'a>,
    field: Field,
) -> Bits<'a> {
    fn helper<'a, T:FiniteField + FromBits + AsBits>(
        c: &CircuitBase<'a>,
        op: UnOp,
        a_bits: Bits<'a>,
        field: Field,
    ) -> Bits<'a> {
        let a_val = T::from_bits(a_bits);
        let val = match op {
            UnOp::Not => panic!("Unsupported operation {:?}", op), // !a_val,
            UnOp::Neg => -a_val,
        };
        val.as_bits(c, field.bit_size())
    }

    match field {
        Field::F40b => helper::<Gf40>(c, op, a_bits, field),
        Field::F45b => helper::<Gf45>(c, op, a_bits, field),
        Field::F56b => helper::<F56b>(c, op, a_bits, field),
        Field::F63b => helper::<F63b>(c, op, a_bits, field),
        Field::F64b => helper::<F64b>(c, op, a_bits, field),
    }
}

pub fn eval_binop_integer<'a>(
    c: &CircuitBase<'a>,
    op: BinOp,
    a_bits: Bits<'a>,
    b_bits: Bits<'a>,
    ty: Ty<'a>,
) -> Bits<'a> {
    let a_val = a_bits.to_bigint(ty);
    let b_val = b_bits.to_bigint(ty);
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
    trunc(c, ty, val)
}

pub fn eval_binop_galois_field<'a>(
    c: &CircuitBase<'a>,
    op: BinOp,
    a_bits: Bits<'a>,
    b_bits: Bits<'a>,
    field: Field,
) -> Bits<'a> {
    fn helper<'a, T:FiniteField + AsBits + FromBits>(
        c: &CircuitBase<'a>,
        op: BinOp,
        a_bits: Bits<'a>,
        b_bits: Bits<'a>,
        field: Field,
    ) -> Bits<'a> {
        let a_val = T::from_bits(a_bits);
        let b_val = T::from_bits(b_bits);
        let val = match op {
            BinOp::Add => a_val + b_val,
            BinOp::Sub => a_val - b_val,
            BinOp::Mul => a_val * b_val,
            BinOp::Div | // safe_div(a_val, b_val),
            BinOp::Mod | // safe_mod(a_val, b_val),
            BinOp::And | // a_val & b_val,
            BinOp::Or  | // a_val | b_val,
            BinOp::Xor => panic!("Unsupported operation {:?}", op), // a_val ^ b_val,
        };
        val.as_bits(c, field.bit_size())
    }

    match field {
        Field::F40b => helper::<Gf40>(c, op, a_bits, b_bits, field),
        Field::F45b => helper::<Gf45>(c, op, a_bits, b_bits, field),
        Field::F56b => helper::<F56b>(c, op, a_bits, b_bits, field),
        Field::F63b => helper::<F63b>(c, op, a_bits, b_bits, field),
        Field::F64b => helper::<F64b>(c, op, a_bits, b_bits, field),
    }
}

pub fn eval_cmp_integer<'a>(
    c: &CircuitBase<'a>,
    op: CmpOp,
    a_bits: Bits<'a>,
    b_bits: Bits<'a>,
    arg_ty: Ty<'a>,
) -> Bits<'a> {
    let a_val = a_bits.to_bigint(arg_ty);
    let b_val = b_bits.to_bigint(arg_ty);
    let val: bool = match op {
        CmpOp::Eq => a_val == b_val,
        CmpOp::Ne => a_val != b_val,
        CmpOp::Lt => a_val <  b_val,
        CmpOp::Le => a_val <= b_val,
        CmpOp::Gt => a_val >  b_val,
        CmpOp::Ge => a_val >= b_val,
    };
    trunc(c, Ty::bool(), val)
}

pub fn eval_cmp_galois_field<'a>(
    c: &CircuitBase<'a>,
    op: CmpOp,
    a_bits: Bits<'a>,
    b_bits: Bits<'a>,
    field: Field,
) -> Bits<'a> {
    fn helper<'a, T:FiniteField + AsBits + FromBits>(
        c: &CircuitBase<'a>,
        op: CmpOp,
        a_bits: Bits<'a>,
        b_bits: Bits<'a>,
    ) -> Bits<'a> {
        let a_val = T::from_bits(a_bits);
        let b_val = T::from_bits(b_bits);
        let val: bool = match op {
            CmpOp::Eq => a_val == b_val,
            CmpOp::Ne => a_val != b_val,
            CmpOp::Lt => panic!("Unsupported operation {:?}", op), // a_val < b_val,
            CmpOp::Le => panic!("Unsupported operation {:?}", op), // a_val <= b_val,
            CmpOp::Gt => panic!("Unsupported operation {:?}", op), // a_val > b_val,
            CmpOp::Ge => panic!("Unsupported operation {:?}", op), // a_val >= b_val,
        };
        trunc(c, Ty::bool(), val)
    }

    match field {
        Field::F40b => helper::<Gf40>(c, op, a_bits, b_bits),
        Field::F45b => helper::<Gf45>(c, op, a_bits, b_bits),
        Field::F56b => helper::<F56b>(c, op, a_bits, b_bits),
        Field::F63b => helper::<F63b>(c, op, a_bits, b_bits),
        Field::F64b => helper::<F64b>(c, op, a_bits, b_bits),
    }
}

fn eval_gate_inner<'a>(
    c: &CircuitBase<'a>,
    ecx: &impl EvalContext<'a>,
    ty: Ty<'a>,
    gk: GateKind<'a>,
) -> Result<(Bits<'a>, bool), Error<'a>> {
    Ok(match gk {
        GateKind::Lit(bits, _) => (bits, false),

        GateKind::Secret(s) => (ecx.eval_secret(s)?, true),

        GateKind::Erased(e) => convert_gate_value(e.gate_value())?,

        GateKind::Argument(i, _) => ecx.eval_argument(i)?,

        GateKind::Unary(op, a) => {
            let (a_bits, a_sec) = ecx.get_value(a)?;
            let result_bits = if a.ty.is_integer() {
                eval_unop_integer(c, op, a_bits, ty)
            } else if let Some(f) = a.ty.get_galois_field() {
                eval_unop_galois_field(c, op, a_bits, f)
            } else {
                panic!("Cannot apply unary operator {:?} on argument {:?}", op, a)
            };
            (result_bits, a_sec)
        },

        GateKind::Binary(op, a, b) => {
            let (a_bits, a_sec) = ecx.get_value(a)?;
            let (b_bits, b_sec) = ecx.get_value(b)?;
            let result_bits = if a.ty.is_integer() {
                eval_binop_integer(c, op, a_bits, b_bits, ty)
            } else if let Some(f) = a.ty.get_galois_field() {
                eval_binop_galois_field(c, op, a_bits, b_bits, f)
            } else {
                panic!("Cannot apply binary operator {:?} on arguments {:?}, {:?}", op, a, b)
            };
            (result_bits, a_sec || b_sec)
        },

        GateKind::Shift(op, a, b) => {
            if a.ty.is_integer() {
                let (a_val, a_sec) = get_int_value(ecx, a)?;
                let (b_val, b_sec) = get_int_value(ecx, b)?;
                let b_val = u16::try_from(b_val).map_err(|_| Error::Other)?;
                let val = match op {
                    ShiftOp::Shl => a_val << b_val,
                    ShiftOp::Shr => a_val >> b_val,
                };
                (trunc(c, ty, val), a_sec || b_sec)
            } else {
                panic!("Cannot apply shift operator {:?} on arguments {:?}, {:?}", op, a, b)
            }
        },

        GateKind::Compare(op, a, b) => {
            let (a_bits, a_sec) = ecx.get_value(a)?;
            let (b_bits, b_sec) = ecx.get_value(b)?;
            let result_bits = if a.ty.is_integer() {
                eval_cmp_integer(c, op, a_bits, b_bits, a.ty)
            } else if let Some(f) = a.ty.get_galois_field() {
                eval_cmp_galois_field(c, op, a_bits, b_bits, f)
            } else {
                panic!("Cannot apply comparison operator {:?} on arguments {:?}, {:?}", op, a, b)
            };
            (result_bits, a_sec || b_sec)
        },

        GateKind::Mux(c, x, y) => {
            if c.ty.is_integer() {
                let (c_val, c_sec) = get_int_value(ecx, c)?;
                // Secrecy: If the condition is public, then the result is only as secret as the chosen
                // input (`x` or `y`).  If the condition is secret, then the result is always secret.
                if !c_val.is_zero() {
                    let (x_bits, x_sec) = ecx.get_value(x)?;
                    (x_bits, x_sec || c_sec)
                } else {
                    let (y_bits, y_sec) = ecx.get_value(y)?;
                    (y_bits, y_sec || c_sec)
                }
            } else {
                panic!("Cannot apply mux operator on arguments {:?}, {:?}, {:?}", c, x, y)
            }
        },

        GateKind::Cast(a, _) => {
            if a.ty.is_integer() && ty.is_integer() {
                let (a_val, a_sec) = get_int_value(ecx, a)?;
                (trunc(c, ty, a_val), a_sec)
            } else {
                panic!("Cannot apply cast on arguments {:?} to {:?}", a, ty)
            }
        },

        GateKind::Pack(ws) => {
            let mut digits = Vec::with_capacity(ty.digits());
            let mut sec = false;
            for &w in ws {
                let (w_bits, w_sec) = ecx.get_value(w)?;
                digits.extend_from_slice(w_bits.0);
                sec |= w_sec;
            }
            let bits = c.intern_bits(&digits);
            (bits, sec)
        },

        GateKind::Extract(w, i) => {
            let (w_bits, w_sec) = ecx.get_value(w)?;
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
                match ecx.get_value(w) {
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

        GateKind::Call(func, args, secrets) => eval_call(c, ecx, func, args, secrets)?,
    })
}

pub fn eval_gate<'a>(
    c: &CircuitBase<'a>,
    ty: Ty<'a>,
    gk: GateKind<'a>,
) -> Result<(Bits<'a>, bool), Error<'a>> {
    eval_gate_inner(c, &TopLevelContext, ty, gk)
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
        return TopLevelContext.get_value(w);
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

    TopLevelContext.get_value(w)
}

fn eval_call<'a, C: CircuitTrait<'a> + ?Sized>(
    c: &C,
    outer_ecx: &impl EvalContext<'a>,
    func: Function<'a>,
    args: &[Wire<'a>],
    secret_args: &[(SecretInputId, Secret<'a>)],
) -> Result<(Bits<'a>, bool), Error<'a>> {
    assert_eq!(secret_args.len(), func.secret_inputs.len());

    let mut num_secrets = func.secret_inputs.iter().map(|&(id, _)| id.0).max()
        .map_or(0, |i| i + 1);
    let mut secrets = vec![None; num_secrets];
    for &(id, s) in secret_args {
        secrets[id.0] = Some(outer_ecx.eval_secret(s)?);
    }

    let mut inner_ecx = FunctionContext {
        args: args.iter().map(|&w| {
            eval_gate_inner(c.as_base(), outer_ecx, w.ty, w.kind)
        }).collect::<Result<Vec<_>, _>>()?,
        secrets,
        cache: HashMap::new(),
    };

    let order = circuit::walk_wires(iter::once(func.result_wire)).collect::<Vec<_>>();
    for w in order {
        let result = eval_gate_inner(c.as_base(), &inner_ecx, w.ty, w.kind)?;
        inner_ecx.cache.insert(w, result);
    }

    Ok(inner_ecx.cache.get(&func.result_wire).cloned().unwrap())
}

pub fn eval_wire_public<'a, C: CircuitTrait<'a> + ?Sized>(c: &C, w: Wire<'a>) -> Option<Value> {
    let (bits, sec) = eval_wire(c, w).ok()?;
    if sec {
        return None;
    }
    Some(Value::from_bits(w.ty, bits))
}

pub fn eval_wire_secret<'a, C: CircuitTrait<'a> + ?Sized>(c: &C, w: Wire<'a>) -> Option<Value> {
    let (bits, _sec) = eval_wire(c, w).ok()?;
    Some(Value::from_bits(w.ty, bits))
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
