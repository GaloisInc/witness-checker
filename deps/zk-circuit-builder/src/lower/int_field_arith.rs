use std::cell::RefCell;
use num_bigint::{BigUint, ToBigInt};
use num_traits::Zero;
use scuttlebutt::field::PrimeFiniteField;
use scuttlebutt::field::F128p;
use crate::ir::circuit::CallData;
use crate::ir::circuit::SwitchCaseData;
use crate::ir::circuit::{CircuitTrait, CircuitExt, CircuitBase, CircuitRef, CircuitFilter, AsBits, FromBits, GateKind, TyKind, Wire, Bits, UnOp::Neg, BinOp::{Add, Sub, Mul, Div, Mod}, Field, IntSize, Ty, Function};
use crate::eval::bigint_to_prime_field_bits;
use crate::ir::migrate::{self, Migrate};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::collections::HashMap;
use std::convert::TryInto;

trait AsField {
    const AS_FIELD: Field;
}

impl AsField for F128p {
    const AS_FIELD: Field = Field::F128p;
}

// Replaces one type with another. If `from_ty` is
// a compound type, recursively replace its components.
// The `to_ty` may only be an atomic (non-compound) type.
//
// For example,
//   * cast_type(Int, F128p) => F128p
//   * cast_type(F128p, Int) => Int
//   * cast_type(Bundle[Int, Int], F128p) => Bundle[cast_type(Int, F128p), cast_type(Int, F128p)] => Bundle[F128p, F128p]
//   * cast_type(Int, Bundle[Int, Int]) => error
//   * cast_type(Bundle[Int, Int], Bundle[F128p, F128p]) => error
fn cast_type<'a>(
    c: &CircuitBase<'a>,
    from_ty: Ty<'a>,
    to_ty: Ty<'a>,
) -> Ty<'a> {
    assert!(!matches!(*to_ty, TyKind::Bundle(_)));
    match *from_ty {
        TyKind::Bundle(btys) => c.ty_bundle(&btys.tys().iter().map(|&ty| cast_type(c, ty, to_ty)).collect::<Vec<_>>()),
        _ => to_ty,
    }
}

fn cast_wire<'a>(
    c: &CircuitBase<'a>,
    w: Wire<'a>,
    ty: Ty<'a>,
) -> Wire<'a> {
    match *w.ty {
        TyKind::Bundle(from_btys) => match *ty {
            TyKind::Bundle(to_btys) => {
                assert_eq!(from_btys.len(), to_btys.len());

                let mut ws = Vec::with_capacity(from_btys.len());
                for i in 0..from_btys.len() {
                    let w_i = cast_wire(c, c.extract(w, i), to_btys.ty(i));
                    ws.push(w_i);
                }
                c.pack(c.wire_list(&ws))
            },
            _ => unreachable!(),
        },
        _ => c.cast(w, ty),
    }
}

fn cast_arguments<'a>(
    c: &CircuitBase<'a>,
    w: Wire<'a>,
    new_tys: &[Ty<'a>],
) -> Wire<'a> {
    let mut cache = HashMap::new();
    cast_arguments_cached(c, &mut cache, w, new_tys)
}

/// Recursively step through the body of a function and re-label each argument `i`
/// as having type `new_ty[i]`, and then cast that argument back to its old type.
fn cast_arguments_cached<'a>(
    c: &CircuitBase<'a>,
    cache: &mut HashMap<Wire<'a>, Wire<'a>>,
    w: Wire<'a>,
    new_tys: &[Ty<'a>],
) -> Wire<'a> {
    if let Some(w_cast) = cache.get(&w).copied() {
        return w_cast;
    }

    let w_cast = match w.kind {
        GateKind::Argument(i, ty) => cast_wire(c, c.gate(GateKind::Argument(i, new_tys[i])), ty),

        GateKind::Lit(_, _) => w,
        GateKind::Secret(secret) => {
            let secret = c.map_secret_deps(secret, |c, deps| {
                let deps_cast = deps.iter()
                    .map(|&dep| cast_arguments_cached(c, cache, dep, new_tys))
                    .collect::<Vec<_>>();
                c.wire_list(&deps_cast)
            });
            c.secret(secret)
        },
        GateKind::Erased(_) => w,
        GateKind::Unary(op, a) => {
            let a = cast_arguments_cached(c, cache, a, new_tys);
            c.unary(op, a)
        },
        GateKind::Binary(op, a, b) => {
            let a = cast_arguments_cached(c, cache, a, new_tys);
            let b = cast_arguments_cached(c, cache, b, new_tys);
            c.binary(op, a, b)
        },
        GateKind::Shift(op, a, b) => {
            let a = cast_arguments_cached(c, cache, a, new_tys);
            let b = cast_arguments_cached(c, cache, b, new_tys);
            c.shift(op, a, b)
        },
        GateKind::Compare(op, a, b) => {
            let a = cast_arguments_cached(c, cache, a, new_tys);
            let b = cast_arguments_cached(c, cache, b, new_tys);
            c.compare(op, a, b)
        },
        GateKind::Mux(cond, a, b) => {
            let cond = cast_arguments_cached(c, cache, cond, new_tys);
            let a = cast_arguments_cached(c, cache, a, new_tys);
            let b = cast_arguments_cached(c, cache, b, new_tys);
            c.mux(cond, a, b)
        },
        GateKind::Cast(w, ty) => {
            let w = cast_arguments_cached(c, cache, w, new_tys);
            c.cast(w, ty)
        },
        GateKind::Pack(ws) => {
            let ws = c.wire_list(&ws.iter().map(|&w| cast_arguments_cached(c, cache, w, new_tys)).collect::<Vec<_>>());
            c.pack(ws)
        },
        GateKind::Extract(w, i) => {
            let w = cast_arguments_cached(c, cache, w, new_tys);
            c.extract(w, i)
        },
        GateKind::Gadget(gadget, args) => {
            let args = c.wire_list(&args.iter().map(|&arg| cast_arguments_cached(c, cache, arg, new_tys)).collect::<Vec<_>>());
            c.gadget(gadget, args)
        },
        GateKind::Call(call) => {
            let CallData { func, args, project_deps, project_witness } = *call;
            let args = c.wire_list(&args.iter().map(|&arg| cast_arguments_cached(c, cache, arg, new_tys)).collect::<Vec<_>>());
            let project_deps = c.wire_list(&project_deps.iter().map(|&dep| cast_arguments_cached(c, cache, dep, new_tys)).collect::<Vec<_>>());
            c.gate(GateKind::Call(c.call_with_secret_project(func, args, project_deps, project_witness)))
        },
        GateKind::Switch(..) => unimplemented!("Lowering nested `GateKind::Switch` is not supported."),
        GateKind::Seq(a, b) => {
            let a = cast_arguments_cached(c, cache, a, new_tys);
            let b = cast_arguments_cached(c, cache, b, new_tys);
            c.seq(a, b)
        },
        GateKind::AssertZero(w) => {
            let w = cast_arguments_cached(c, cache, w, new_tys);
            c.assert_zero(w)
        },
    };
    cache.insert(w, w_cast);
    w_cast
}

fn int_field_arith<'a, F: PrimeFiniteField + AsField + FromBits + AsBits>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    // We pass `arith_func_map` as `&RefCell<T>` instead of `&mut T` to prevent having a long-lived
    // borrow across the call to `int_field_arith`.  This prevents a panic in cases where
    // `int_field_arith` is reentrant.
    arith_func_map: &RefCell<HashMap<Function<'a>, Function<'a>>>,
    gk: GateKind<'a>,
) -> Option<Wire<'a>>
where
    F::Error: Debug,
{
    let ty = gk.ty(c);

    let field_ty = c.ty(TyKind::GF(F::AS_FIELD));
    let field_width = F::AS_FIELD.bit_size().bits();
    let field_size = F::AS_FIELD.modulus().unwrap();
    match gk {
        GateKind::Unary(Neg, a) if ty.is_integer() => {
            let ty_width = ty.integer_size().bits();
            assert!(ty_width + 1 < field_width);
            let a_f = c.cast(a, field_ty);
            // TODO(isweet): A little ugly to compute this above as `ty_size`
            // and again here, but `F` and `BigUint` are different types and
            // converting between them is a pain.
            let two_f = F::try_from(2 as u128).unwrap();
            let max_f = c.lit(field_ty, two_f.pow(ty.integer_size().bits() as u128));
            let neg_a_f = c.sub(max_f, a_f);
            let ret = c.cast(neg_a_f, ty);
            Some(ret)
        },
        GateKind::Binary(Add, a, b) if ty.is_integer() => {
            let ty_width = ty.integer_size().bits();
            assert!(ty_width + 1 < field_width);
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let sum_f = c.add(a_f, b_f);
            let ret = c.cast(sum_f, ty);
            Some(ret)
        },
        GateKind::Binary(Sub, a, b) if ty.is_integer() => {
            let ty_width = ty.integer_size().bits();
            assert!(ty_width + 2 < field_width);
            // This is necessary to prevent underflowing the field, which
            // is handled by the negation gate.
            let ret = c.add(a, c.neg(b));
            Some(ret)
        },
        GateKind::Binary(Mul, a, b) if ty.is_integer() => {
            let ty_width = ty.integer_size().bits();
            let ty_size = BigUint::from(2_u64).pow(ty_width as u32);
            // For (unsigned) integers of width `w`, the maximum result
            // of multiplication is (2^w - 1)^2. There is a margin between
            // that value and 2^(2 * w) - 1, which is the largest value
            // representable in double the number of bits. So, GF(p) can
            // represent the result of a width `w` multiplication as long
            // as (2^w - 1)^2 < `p`.
            assert!((ty_size - BigUint::from(1_u32)).pow(2_u32) < field_size);
            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let prod_f = c.mul(a_f, b_f);
            let ret = c.cast(prod_f, ty);
            Some(ret)
        },
        GateKind::Binary(op @ Div, a, b) | GateKind::Binary(op @ Mod, a, b) if ty.is_uint() => {
            let width = ty.integer_size();
            let quot_f = c.secret_derived(field_ty, c.wire_list(&[a, b]), move |c, vs| {
                let [a_bits, b_bits]: [Bits; 2] = vs.try_into().unwrap();
                let a = a_bits.to_biguint();
                let b = b_bits.to_biguint();
                let quot = if b.is_zero() { BigUint::zero() } else { a / b };
                bigint_to_prime_field_bits(c, quot.to_bigint().unwrap(), width, F::AS_FIELD)
            });
            let rem_f = c.secret_derived(field_ty, c.wire_list(&[a, b]), move |c, vs| {
                let [a_bits, b_bits]: [Bits; 2] = vs.try_into().unwrap();
                let a = a_bits.to_biguint();
                let b = b_bits.to_biguint();
                let rem = if b.is_zero() { a } else { a % b };
                bigint_to_prime_field_bits(c, rem.to_bigint().unwrap(), width, F::AS_FIELD)
            });

            let a_f = c.cast(a, field_ty);
            let b_f = c.cast(b, field_ty);
            let quot_times_denom_f = c.mul(quot_f, b_f);               // q * b
            let num_minus_rem_f = c.sub(a_f, rem_f);                   // a - r
            let diff_all = c.sub(quot_times_denom_f, num_minus_rem_f); // (q * b) - (a - r)

            let width = (*b.ty).integer_size().bits();
            let neg_check_ty = c.ty(TyKind::Int(IntSize(width + 1)));
            let rem_int = c.cast(rem_f, neg_check_ty);
            let b_int = c.cast(b, neg_check_ty);
            let rem_minus_denom = c.sub(rem_int, b_int);                                // r - b
            let rem_minus_denom_is_neg = c.lt(rem_minus_denom, c.lit(neg_check_ty, 0)); // r - b < 0 (i.e. r < b)
            let denom_zero = c.eq(b, c.lit(b.ty, 0));                                   // b == 0
            let ok = c.or(rem_minus_denom_is_neg, denom_zero);                          // r < b \/ b == 0

            // Asserts that q * b - (a - r) == 0 (which implies that a == q * b + r)
            let ret = c.seq(c.assert_zero(diff_all), {
                // Asserts that either the remainder is less than the denominator, or the denominator is zero
                c.seq(c.assert_zero(c.not(ok)), c.cast(match op {
                    Div => quot_f,
                    Mod => rem_f,
                    _   => unreachable!(),
                }, ty))
            });
            Some(ret)
        },
        GateKind::Switch(guard, cases, args) if guard.ty.is_integer() => {
            let guard_f = c.cast(guard, field_ty);
            let arg_tys = args.iter().map(|&arg| cast_type(c.as_base(), arg.ty, field_ty)).collect::<Vec<_>>();
            let cases_f = c.switch_case_list(&cases.iter().map(|&case| {
                let SwitchCaseData { pattern, body, project_deps, project_witness } = *case;
                let pattern_f = crate::eval::bigint_to_prime_field_bits(c.as_base(), pattern.to_bigint(guard.ty), guard.ty.integer_size(), F::AS_FIELD);
                let opt_arith_body = arith_func_map.borrow().get(&body).copied();
                let body_f = if let Some(arith_body) = opt_arith_body {
                    arith_body
                } else {
                    let arith_body = c.as_base().map_function(body, |c, _, result| {
                        let result_ty = cast_type(c.as_base(), result.ty, field_ty);
                        let result = cast_wire(c.as_base(), cast_arguments(c.as_base(), result, &arg_tys), result_ty);
                        (c.ty_list(&arg_tys), result)
                    });
                    let old = arith_func_map.borrow_mut().insert(body, arith_body);
                    assert!(old.is_none(), "duplicate conversion of function {:?}?", body);
                    arith_body
                };
                c.switch_case_with_secret_project(pattern_f, body_f, project_deps, project_witness)
            }).collect::<Vec<_>>());
            let args_f = c.wire_list(&args.iter().enumerate().map(|(i, &arg)| cast_wire(c.as_base(), arg, arg_tys[i])).collect::<Vec<_>>());
            let result = c.switch(guard_f, cases_f, args_f);
            Some(cast_wire(c.as_base(), result, ty))
        },
        _ => None,
    }
}

struct NumBounds {
    _valid_bits: u16,
    _real_bits: u16,
}

pub struct IntFieldArith<'a, F, P> {
    inner: F,
    _field: PhantomData<P>,
    active: bool,
    bounds: HashMap<Wire<'a>, NumBounds>,
    /// Map from original function definition to a version where all inputs and outputs are
    /// converted to arithmetic types.
    arith_func_map: RefCell<HashMap<Function<'a>, Function<'a>>>,
}

impl<'a, F, P> IntFieldArith<'a, F, P> {
    pub fn new(inner: F, active: bool) -> Self {
        IntFieldArith {
            inner,
            _field: PhantomData,
            active,
            bounds: HashMap::new(),
            arith_func_map: RefCell::new(HashMap::new()),
        }
    }
}

impl<'a, F: CircuitFilter<'a> + 'a, P: PrimeFiniteField + AsField + FromBits + AsBits> CircuitFilter<'a> for IntFieldArith<'a, F, P>
where F: Migrate<'a, 'a, Output = F>,
      P::Error: Debug,
{
    circuit_filter_common_methods!();

    fn gate(&self, base: &CircuitBase<'a>, gk: GateKind<'a>) -> Wire<'a> {
        let c = CircuitRef { base, filter: &self.inner };

        if self.active {
            let c = CircuitRef { base, filter: self };
            if let Some(w) = int_field_arith::<P>(&c, &self.arith_func_map, gk) {
                return w;
            }
        }

        c.gate(gk)
    }
}

impl<'a, 'b, F, P> Migrate<'a, 'b> for IntFieldArith<'a, F, P>
where
    F: Migrate<'a, 'b>,
{
    type Output = IntFieldArith<'b, F::Output, P>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        let mut bounds = HashMap::new();
        for (old_wire, old_repr) in self.bounds {
            let new_wire = match v.visit_wire_weak(old_wire) {
                Some(x) => x,
                None => continue,
            };

            bounds.insert(new_wire, old_repr);
        }

        IntFieldArith {
            inner: v.visit(self.inner),
            _field: PhantomData,
            active: self.active,
            bounds,
            arith_func_map: v.visit(self.arith_func_map),
        }
    }
}
