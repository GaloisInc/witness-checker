use zkinterface_bellman::sapling_crypto::circuit::uint32::UInt32;
use zkinterface_bellman::bellman::{ConstraintSystem, SynthesisError};
use zkinterface_bellman::pairing::Engine;
use zkinterface_bellman::ff::PrimeField;
use zkinterface_bellman::sapling_crypto::circuit::boolean::Boolean;
use crate::back::zkif::representer::{fr_from_unsigned};
use crate::back::zkif::num::Num;

pub fn bitwise_xor<E: Engine, CS: ConstraintSystem<E>>(
    cs: CS,
    left: &UInt32,
    right: &UInt32,
) -> UInt32
{
    left.xor(cs, right).unwrap()
}

// TODO: Implement directly on the type but fields are private.
pub fn bitwise_and<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    left: &UInt32,
    right: &UInt32,
) -> UInt32
{
    let lbits = left.into_bits();
    let rbits = right.into_bits();

    let out_bits: Vec<Boolean> =
        lbits.iter()
            .zip(rbits.iter())
            .map(|(l, r)|
                Boolean::and(&mut cs, l, r).unwrap()
            ).collect();

    UInt32::from_bits(&out_bits)
}

pub fn bitwise_or<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: &mut CS,
    left: &UInt32,
    right: &UInt32,
) -> UInt32
{
    let lbits = left.into_bits();
    let rbits = right.into_bits();

    let out_bits: Vec<Boolean> =
        lbits.iter()
            .zip(rbits.iter())
            .map(|(l, r)|
                bool_or(&mut cs, l, r)
            ).collect();

    UInt32::from_bits(&out_bits)
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
    numer_int: &UInt32,
    denom_num: &Num<E>,
    denom_int: &UInt32,
) -> (/*quotient*/ UInt32, /*rest*/ UInt32) {
    let (quot_val, rest_val) = match (&numer_num.value, &denom_num.value) {
        (
            Some(ref numer_val),
            Some(ref denom_val)
        ) => {
            // TODO: use UInt32.value but it is private.
            let numer = {
                let repr = numer_val.into_repr();
                let limbs = repr.as_ref();
                limbs[0] as u32
            };
            let denom = {
                let repr = denom_val.into_repr();
                let limbs = repr.as_ref();
                limbs[0] as u32
            };
            let quot_val = numer / denom;
            let rest_val = numer % denom;
            (Some(quot_val), Some(rest_val))
        }

        _ => (None, None)
    };

    let quot_num = Num::alloc(&mut cs, quot_val).unwrap();
    let rest_num = Num::alloc(&mut cs, rest_val).unwrap();

    cs.enforce(
        || "division",
        |lc| lc + &quot_num.lc,
        |lc| lc + &denom_num.lc,
        |lc| lc + &numer_num.lc - &rest_num.lc,
    );

    // Convert to enforce the integer sizes.
    // TODO: actual conversion from quotient_num and rest_num.
    let quot_int = UInt32::alloc(&mut cs, quot_val).unwrap();
    let rest_int = UInt32::alloc(&mut cs, rest_val).unwrap();

    // TODO: verify that rest<denom.

    (quot_int, rest_int)
}