use zkinterface_bellman::sapling_crypto::circuit::uint32::UInt32;
use zkinterface_bellman::bellman::{ConstraintSystem, SynthesisError};
use zkinterface_bellman::pairing::Engine;
use zkinterface_bellman::sapling_crypto::circuit::boolean::Boolean;

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