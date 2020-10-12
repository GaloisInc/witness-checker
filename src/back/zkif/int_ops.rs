use std::cmp;
use num_traits::Zero;
use zkinterface_bellman::{
    bellman::{ConstraintSystem, SynthesisError, LinearCombination},
    bellman::gadgets::boolean::Boolean,
    pairing::Engine,
    ff::PrimeField,
    zkif_cs::ZkifCS,
};
use super::{
    num::{Num, boolean_lc, scalar_from_unsigned},
    int::Int,
    bit_width::BitWidth,
};

pub fn bitwise_xor<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    cs: CS,
    left: &Int,
    right: &Int,
) -> Int
{
    left.xor(cs, right).unwrap()
}

// TODO: Implement directly on the type but fields are private.
pub fn bitwise_and<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    left: &Int,
    right: &Int,
) -> Int
{
    let out_bits: Vec<Boolean> =
        left.bits.iter()
            .zip(right.bits.iter())
            .map(|(l, r)|
                Boolean::and(&mut cs, l, r).unwrap()
            ).collect();

    Int::from_bits(&out_bits)
}

pub fn bitwise_or<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: &mut CS,
    left: &Int,
    right: &Int,
) -> Int
{
    let out_bits: Vec<Boolean> =
        left.bits.iter()
            .zip(right.bits.iter())
            .map(|(l, r)|
                bool_or(&mut cs, l, r)
            ).collect();

    Int::from_bits(&out_bits)
}

pub fn bool_or<'a, Scalar, CS>(
    cs: CS,
    a: &'a Boolean,
    b: &'a Boolean,
) -> Boolean
    where Scalar: PrimeField,
          CS: ConstraintSystem<Scalar>
{
    Boolean::and(cs, &a.not(), &b.not()).unwrap().not()
}

pub fn enforce_true<Scalar, CS>(
    mut cs: CS,
    bool: &Boolean,
) where Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>
{
    cs.enforce(
        || "enforce true",
        |_| boolean_lc::<Scalar, CS>(bool),
        |lc| lc + CS::one(),
        |lc| lc + CS::one(),
    );
}

pub fn div<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    numer_num: &Num<Scalar>,
    numer_int: &Int,
    denom_num: &Num<Scalar>,
    denom_int: &Int,
) -> (/*quotient*/ Num<Scalar>, Int, /*rest*/ Num<Scalar>, Int) {
    let (quot_val, rest_val) = match (numer_int.value.as_ref(), denom_int.value.as_ref()) {
        (Some(numer), Some(denom)) => {
            if denom.is_zero() {
                (Some(0_u8.into()), Some(numer.clone()))
            } else {
                let quot_val = numer / denom;
                let rest_val = numer % denom;
                (Some(quot_val), Some(rest_val))
            }
        }
        _ => (None, None)
    };

    let max_width = cmp::max(numer_int.width(), denom_int.width());
    let quot_int = Int::alloc(&mut cs, max_width, quot_val).unwrap();
    let rest_int = Int::alloc(&mut cs, denom_int.width(), rest_val).unwrap();

    let quot_num = Num::from_int::<CS>(&quot_int);
    let rest_num = Num::from_int::<CS>(&rest_int);

    // Verify that: numerator == quotient * denominator + rest.
    cs.enforce(
        || "division",
        |lc| lc + &quot_num.lc,
        |lc| lc + &denom_num.lc,
        |lc| lc + &numer_num.lc - &rest_num.lc,
    );

    // Verify that rest < denom || denom == 0.
    let diff_num = rest_num.clone().sub(&denom_num, &mut cs).unwrap();
    let diff_int = Int::from_num(&mut cs, denom_int.width(), &diff_num);
    let diff_ok = diff_int.is_negative();
    let denom_zero = denom_num.equals_zero(&mut cs);
    let ok = bool_or(&mut cs, &diff_ok, &denom_zero);
    let one = CS::one();
    cs.enforce(
        || "rest < denom",
        |lc| lc + one,
        |lc| lc + one,
        |_| boolean_lc::<Scalar, CS>(&ok),
    );
    // TODO: this should be done without enforce but by construction of diff_int.

    (quot_num, quot_int, rest_num, rest_int)
}
