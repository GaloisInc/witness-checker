use zkinterface_bellman::{
    bellman::{ConstraintSystem, SynthesisError, LinearCombination},
    bellman::gadgets::boolean::Boolean,
    pairing::Engine,
    ff::PrimeField,
};
use super::{
    zkif_cs::{scalar_from_unsigned, ZkifCS},
    num::{Num, boolean_lc},
    int64::Int64,
    bit_width::BitWidth,
};

pub fn bitwise_xor<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    cs: CS,
    left: &Int64,
    right: &Int64,
) -> Int64
{
    left.xor(cs, right).unwrap()
}

// TODO: Implement directly on the type but fields are private.
pub fn bitwise_and<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    left: &Int64,
    right: &Int64,
) -> Int64
{
    let out_bits: Vec<Boolean> =
        left.bits.iter()
            .zip(right.bits.iter())
            .map(|(l, r)|
                Boolean::and(&mut cs, l, r).unwrap()
            ).collect();

    Int64::from_bits(&out_bits)
}

pub fn bitwise_or<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: &mut CS,
    left: &Int64,
    right: &Int64,
) -> Int64
{
    let out_bits: Vec<Boolean> =
        left.bits.iter()
            .zip(right.bits.iter())
            .map(|(l, r)|
                bool_or(&mut cs, l, r)
            ).collect();

    Int64::from_bits(&out_bits)
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
    numer_int: &Int64,
    denom_num: &Num<Scalar>,
    denom_int: &Int64,
) -> (/*quotient*/ Num<Scalar>, Int64, /*rest*/ Num<Scalar>, Int64) {
    let (quot_val, rest_val) = match (numer_int.value, denom_int.value) {
        (Some(numer), Some(denom)) => {
            if denom == 0 {
                panic!("Attempt to divide by zero");
                //(Some(0), Some(numer))
            } else {
                let quot_val = numer / denom;
                let rest_val = numer % denom;
                (Some(quot_val), Some(rest_val))
            }
        }
        _ => (None, None)
    };

    let quot_int = Int64::alloc(&mut cs, quot_val).unwrap();
    let rest_int = Int64::alloc(&mut cs, rest_val).unwrap();
    // TODO: optimize the integer sizes.

    let quot_num = Num::from_int::<CS>(&quot_int);
    let rest_num = Num::from_int::<CS>(&rest_int);

    // Verify that: numerator == quotient * denominator + rest.
    cs.enforce(
        || "division",
        |lc| lc + &quot_num.lc,
        |lc| lc + &denom_num.lc,
        |lc| lc + &numer_num.lc - &rest_num.lc,
    );

    // Verify that rest < denom.
    let diff_num = rest_num.clone() - denom_num;
    let diff_int = Int64::from_num(&mut cs, &diff_num);
    let ok = diff_int.is_negative();
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
