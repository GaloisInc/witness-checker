use zkinterface_bellman::{
    bellman::{ConstraintSystem, SynthesisError, LinearCombination},
    pairing::Engine,
    ff::PrimeField,
    sapling_crypto::circuit::boolean::Boolean,
};
use super::{
    zkif_cs::{fr_from_unsigned, ZkifCS},
    num::{Num, boolean_lc},
    int32::Int32,
    bit_width::BitWidth,
};

pub fn bitwise_xor<E: Engine, CS: ConstraintSystem<E>>(
    cs: CS,
    left: &Int32,
    right: &Int32,
) -> Int32
{
    left.xor(cs, right).unwrap()
}

// TODO: Implement directly on the type but fields are private.
pub fn bitwise_and<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    left: &Int32,
    right: &Int32,
) -> Int32
{
    let out_bits: Vec<Boolean> =
        left.bits.iter()
            .zip(right.bits.iter())
            .map(|(l, r)|
                Boolean::and(&mut cs, l, r).unwrap()
            ).collect();

    Int32::from_bits(&out_bits)
}

pub fn bitwise_or<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: &mut CS,
    left: &Int32,
    right: &Int32,
) -> Int32
{
    let out_bits: Vec<Boolean> =
        left.bits.iter()
            .zip(right.bits.iter())
            .map(|(l, r)|
                bool_or(&mut cs, l, r)
            ).collect();

    Int32::from_bits(&out_bits)
}

pub fn bool_or<'a, E, CS>(
    cs: CS,
    a: &'a Boolean,
    b: &'a Boolean,
) -> Boolean
    where E: Engine,
          CS: ConstraintSystem<E>
{
    Boolean::and(cs, &a.not(), &b.not()).unwrap().not()
}


pub fn div<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    numer_num: &Num<E>,
    numer_int: &Int32,
    denom_num: &Num<E>,
    denom_int: &Int32,
) -> (/*quotient*/ Num<E>, Int32, /*rest*/ Num<E>, Int32) {
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

    let quot_int = Int32::alloc(&mut cs, quot_val).unwrap();
    let rest_int = Int32::alloc(&mut cs, rest_val).unwrap();
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
    let diff_int = Int32::from_num(&mut cs, &diff_num);
    let ok = diff_int.is_negative();
    let one = CS::one();
    cs.enforce(
        || "rest < denom",
        |lc| lc + one,
        |lc| lc + one,
        |_| boolean_lc::<E, CS>(&ok),
    );
    // TODO: this should be done without enforce but by construction of diff_int.

    (quot_num, quot_int, rest_num, rest_int)
}
