// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use std::ops::{Add, Sub, Mul, AddAssign};
use num_bigint::{BigUint, BigInt, Sign};

use zkinterface_bellman::{
    bellman::{ConstraintSystem, LinearCombination, SynthesisError, Variable},
    bellman::gadgets::boolean::{AllocatedBit, Boolean},
    pairing::Engine,
    ff::{Field, PrimeField},
    zkif_cs::ZkifCS,
};
use super::{
    bit_width::BitWidth,
    int::Int,
};


/// A number, represented as a single field element.
#[derive(Clone)]
pub struct Num<Scalar: PrimeField> {
    pub value: Option<Scalar>,
    pub lc: LinearCombination<Scalar>,
    /// How many bits would be required to represent this number.
    pub bit_width: BitWidth,
}

impl<Scalar: PrimeField> From<u64> for Num<Scalar> {
    fn from(literal: u64) -> Self {
        let element: Scalar = scalar_from_unsigned(literal);
        Num {
            value: Some(element.clone()),
            lc: LinearCombination::zero() + (element, ZkifCS::<Scalar>::one()),
            bit_width: BitWidth::from(literal),
        }
    }
}

impl<Scalar: PrimeField> From<i64> for Num<Scalar> {
    fn from(literal: i64) -> Self {
        let element: Scalar = scalar_from_signed(literal);
        Num {
            value: Some(element.clone()),
            lc: LinearCombination::zero() + (element, ZkifCS::<Scalar>::one()),
            bit_width: BitWidth::from(literal),
        }
    }
}

impl<Scalar: PrimeField> Num<Scalar> {
    pub fn zero() -> Self {
        Num {
            value: Some(Scalar::zero()),
            lc: LinearCombination::zero(),
            bit_width: BitWidth::zero(),
        }
    }

    pub fn _alloc<CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        value: Option<u64>,
    ) -> Result<Self, SynthesisError>
    {
        let value = value.map(|val| Scalar::from(val));
        let var = cs.alloc(|| "num", ||
            value.ok_or(SynthesisError::AssignmentMissing))?;
        Ok(Num {
            value,
            lc: LinearCombination::zero() + var,
            bit_width: BitWidth::Unknown, // u64 is used but we did not prove it.
        })
    }

    pub fn from_int<CS: ConstraintSystem<Scalar>>(
        int: &Int,
    ) -> Num<Scalar> {
        let value = int.value.as_ref().map(scalar_from_biguint);

        let lc = Self::lc_from_bits::<CS>(&int.bits);

        let bit_width = BitWidth::from(int);

        Num { value, lc, bit_width }
    }

    pub fn lc_from_bits<CS: ConstraintSystem<Scalar>>(
        bits: &[Boolean]) -> LinearCombination<Scalar>
    {
        let mut lc = LinearCombination::zero();
        let one = CS::one();
        let mut coeff = Scalar::one();
        for bit in bits {
            lc = lc + &bit.lc(one, coeff);
            coeff = coeff.double();
        }
        lc
    }

    pub fn from_boolean<CS: ConstraintSystem<Scalar>>(
        bool: &Boolean,
    ) -> Self {
        Num {
            value: bool.get_value().map(|b|
                if b { Scalar::one() } else { Scalar::zero() }
            ),
            lc: boolean_lc::<Scalar, CS>(bool),
            bit_width: BitWidth::from(bool),
        }
    }

    /// Decompose this number into bits, least-significant first.
    /// Negative numbers are encoded in two-complement.
    pub fn alloc_bits<CS: ConstraintSystem<Scalar>>(
        &self, cs: CS) -> Vec<Boolean>
    {
        self.assert_no_overflow();

        match self.bit_width {
            BitWidth::Unknown => panic!("Cannot decompose a number of unknown size."),

            BitWidth::Max(_, false) =>
                self.alloc_bits_unsigned(cs),

            BitWidth::Max(width, true) => {
                // Shift the number to be centered around the next power of two.
                let offset = Self::power_of_two::<CS>(width);
                // This cannot over- or underflow so we don't extend the bit width.
                let shifted = offset.add_unsafe(self);
                // Encode as a positive number.
                let mut bits = shifted.alloc_bits_unsigned(cs);
                assert_eq!(bits.len(), width + 1);
                // Substract the offset by flipping the corresponding bit.
                bits[width] = bits[width].not();
                // bits is now a two-complement encoding of the signed number.
                bits
            }
        }
    }

    fn alloc_bits_unsigned<CS: ConstraintSystem<Scalar>>(
        &self, mut cs: CS) -> Vec<Boolean>
    {
        let n_bits = match self.bit_width {
            BitWidth::Max(n_bits, false) => n_bits,
            _ => panic!("Cannot decompose a negative or unsized number."),
        };

        let values: Vec<Option<bool>> = match &self.value {
            Some(val) => {
                let bits = val.to_le_bits();
                bits.iter().take(n_bits).map(|b| Some(*b)).collect()
            }
            None => vec![None; n_bits]
        };

        let bits: Vec<Boolean> = values.into_iter()
            .enumerate()
            .map(|(i, val)|
                Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("allocated bit {}", i)),
                    val,
                ).unwrap())
            ).collect();

        let lc = Self::lc_from_bits::<CS>(&bits);

        cs.enforce(
            || "bit decomposition",
            |zero| zero,
            |zero| zero,
            |_| lc - &self.lc,
        );
        // TODO: this could be optimized by deducing one of the bits from num instead of checking equality.

        bits
    }

    /// Assert that no overflows could occur in computing this Num.
    pub fn assert_no_overflow(&self) {
        if !self.bit_width.fits_into(Scalar::CAPACITY as usize) {
            panic!("Number may overflow (size {:?}).", self.bit_width);
        }
    }

    pub fn mul(mut self, other: &Self,
               cs: &mut impl ConstraintSystem<Scalar>,
    ) -> Self {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.mul_assign(other_val),

            _ => {}
        }

        let product = cs.alloc(
            || "product",
            || self.value.ok_or(SynthesisError::AssignmentMissing),
        ).unwrap();
        let product_lc = LinearCombination::<Scalar>::zero() + product;

        cs.enforce(
            || "multiplication",
            |lc| lc + &self.lc,
            |lc| lc + &other.lc,
            |lc| lc + &product_lc,
        );

        self.lc = product_lc;
        self.bit_width = self.bit_width.mul(other.bit_width);
        self
    }

    pub fn equals_zero<CS: ConstraintSystem<Scalar>>(
        &self,
        cs: &mut CS,
    ) -> Boolean {
        let is_zero = {
            let value = self.value.map(|val| val.is_zero());
            Boolean::from(AllocatedBit::alloc::<Scalar, &mut CS>(
                cs, value).unwrap())
        };
        let is_zero_lc = boolean_lc::<Scalar, CS>(&is_zero);

        cs.enforce(
            || "eq=1 => self=0",
            |lc| lc + &self.lc,
            |lc| lc + &is_zero_lc,
            |lc| lc,
        );

        let self_inv = cs.alloc(
            || "inv",
            || Ok(
                self.value.unwrap().invert()
                    .unwrap_or_else(|| Scalar::zero())
            ),
        ).unwrap();
        cs.enforce(
            || "self=0 => eq=1",
            |lc| lc + &self.lc,
            |lc| lc + self_inv,
            |lc| lc + CS::one() - &is_zero_lc,
        );

        // TODO: should be doable without the boolean constraint of AllocatedBit.
        is_zero
    }

    // TODO: cache.
    pub fn power_of_two<CS: ConstraintSystem<Scalar>>(n: usize) -> Self
    {
        let mut element = Scalar::one();
        for _ in 0..n {
            element = element.double();
        }

        Num::<Scalar> {
            value: Some(element.clone()),
            lc: LinearCombination::zero() + (element, CS::one()),
            bit_width: BitWidth::Max(n + 1, false),
        }
    }

    /// Add without tracking the bit width.
    fn add_unsafe(mut self, other: &Self) -> Self {
        let original_width = self.bit_width.clone();
        self = self + other;
        self.bit_width = original_width;
        self
    }
}

impl<'a, Scalar: PrimeField> Add<&'a Num<Scalar>> for Num<Scalar> {
    type Output = Num<Scalar>;

    fn add(mut self, other: &'a Num<Scalar>) -> Num<Scalar> {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.add_assign(other_val),

            _ => {}
        }

        self.lc = self.lc + &other.lc;
        self.bit_width = self.bit_width.add(other.bit_width);
        self
    }
}

impl<'a, Scalar: PrimeField> Sub<&'a Num<Scalar>> for Num<Scalar> {
    type Output = Num<Scalar>;

    fn sub(mut self, other: &'a Num<Scalar>) -> Num<Scalar> {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.sub_assign(other_val),

            _ => {}
        }

        self.lc = self.lc - &other.lc;
        self.bit_width = self.bit_width.sub(other.bit_width);
        self
    }
}


pub fn boolean_lc<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    bool: &Boolean,
) -> LinearCombination<Scalar> {
    bool.lc(CS::one(), Scalar::one())
}


pub fn scalar_from_unsigned<Scalar: PrimeField>(val: u64) -> Scalar {
    Scalar::from(val)
}

pub fn scalar_from_signed<Scalar: PrimeField>(val: i64) -> Scalar {
    if val >= 0 {
        scalar_from_unsigned::<Scalar>(val as u64)
    } else {
        scalar_from_unsigned::<Scalar>((-val) as u64).neg()
    }
}

pub fn scalar_from_biguint<Scalar: PrimeField>(val: &BigUint) -> Scalar {
    let bytes = val.to_bytes_le();
    let mut repr: Scalar::Repr = Default::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes);
    Scalar::from_repr(repr)
        .expect("uint out of range for Scalar")
}

pub fn scalar_from_bigint<Scalar: PrimeField>(val: &BigInt) -> Scalar {
    let (sign, bytes) = val.to_bytes_le();
    let mut repr: Scalar::Repr = Default::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes);
    let scalar = Scalar::from_repr(repr)
        .expect("uint out of range for Scalar");
    match sign {
        Sign::Minus => scalar.neg(),
        Sign::Plus | Sign::NoSign => scalar,
    }
}


#[test]
fn test_num() -> Result<(), Box<dyn std::error::Error>> {
    use super::field::QuarkScalar;
    use zkinterface_bellman::export::encode_scalar;

    let n = Num::<QuarkScalar>::from((3u64 << 8) + (5u64 << 32));
    let val = n.value.unwrap();
    let expected = vec![0, 3, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 as u8];

    let mut encoded = vec![];
    encode_scalar(&val, &mut encoded);
    assert_eq!(encoded, expected);

    Ok(())
}
