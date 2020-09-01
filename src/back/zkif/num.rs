// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use std::ops::{Add, Sub, Mul};

use zkinterface_bellman::{
    bellman::{ConstraintSystem, LinearCombination, SynthesisError, Variable},
    sapling_crypto::circuit::boolean::{Boolean, AllocatedBit},
    pairing::Engine,
    ff::{ScalarEngine, Field, PrimeField, PrimeFieldRepr},
};
use super::{
    zkif_cs::{En, Fr, LC, ZkifCS, fr_from_signed, fr_from_unsigned},
    bit_width::BitWidth,
    int32::Int32,
};


#[derive(Clone)]
pub struct Num<E: Engine> {
    pub value: Option<E::Fr>,
    pub lc: LinearCombination<E>,
    /// How many bits would be required to represent this number.
    pub bit_width: BitWidth,
}

impl From<u64> for Num<En> {
    fn from(literal: u64) -> Self {
        let element: Fr = fr_from_unsigned(literal);
        Num {
            value: Some(element.clone()),
            lc: LC::zero() + (element, ZkifCS::one()),
            bit_width: BitWidth::from(literal),
        }
    }
}

impl From<i64> for Num<En> {
    fn from(literal: i64) -> Self {
        let element: Fr = fr_from_signed(literal);
        Num {
            value: Some(element.clone()),
            lc: LC::zero() + (element, ZkifCS::one()),
            bit_width: BitWidth::from(literal),
        }
    }
}

impl<E: Engine> Num<E> {
    pub fn zero() -> Self {
        Num {
            value: Some(E::Fr::zero()),
            lc: LinearCombination::zero(),
            bit_width: BitWidth::zero(),
        }
    }

    pub fn _alloc<CS: ConstraintSystem<E>>(
        mut cs: CS,
        value: Option<u32>,
    ) -> Result<Self, SynthesisError>
    {
        let value = value.map(|val|
            E::Fr::from_repr(<<E::Fr as PrimeField>::Repr as From<u64>>::
            from(val as u64)).unwrap()
        );
        let var = cs.alloc(|| "num", ||
            value.ok_or(SynthesisError::AssignmentMissing))?;
        Ok(Num {
            value,
            lc: LinearCombination::zero() + var,
            bit_width: BitWidth::Unknown, // u32 is used but we did not prove it.
        })
    }

    pub fn from_int<CS: ConstraintSystem<E>>(
        int: &Int32,
    ) -> Num<E> {
        let value = int.value.map(|val|
            fr_from_unsigned(val as u64));

        let lc = Self::lc_from_bits::<CS>(&int.bits);

        let bit_width = BitWidth::from(int);

        Num { value, lc, bit_width }
    }

    pub fn lc_from_bits<CS: ConstraintSystem<E>>(
        bits: &[Boolean]) -> LinearCombination<E>
    {
        let mut lc = LinearCombination::zero();
        let one = CS::one();
        let mut coeff = E::Fr::one();
        for bit in bits {
            lc = lc + &bit.lc(one, coeff);
            coeff.double();
        }
        lc
    }

    pub fn from_boolean<CS: ConstraintSystem<E>>(
        bool: &Boolean,
    ) -> Self {
        Num {
            value: bool.get_value().map(|b|
                if b { E::Fr::one() } else { E::Fr::zero() }
            ),
            lc: boolean_lc::<E, CS>(bool),
            bit_width: BitWidth::from(bool),
        }
    }

    /// Decompose this number into bits, least-significant first.
    /// Negative numbers are encoded in two-complement.
    pub fn alloc_bits<CS: ConstraintSystem<E>>(
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

    fn alloc_bits_unsigned<CS: ConstraintSystem<E>>(
        &self, mut cs: CS) -> Vec<Boolean>
    {
        let n_bits = match self.bit_width {
            BitWidth::Max(n_bits, false) => n_bits,
            _ => panic!("Cannot decompose a negative or unsized number."),
        };

        let values = match &self.value {
            Some(val) => {
                let repr = val.into_repr();
                let limbs: &[u64] = repr.as_ref();
                let mut bools = Vec::with_capacity(n_bits);

                for i_bit in 0..n_bits {
                    let which_limb = i_bit / 64;
                    let which_bit = i_bit % 64;
                    let bit = (limbs[which_limb] >> which_bit) & 1 == 1;
                    bools.push(Some(bit));
                }

                bools
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
        if !self.bit_width.fits_into(E::Fr::CAPACITY as usize) {
            panic!("Number may overflow (size {:?}).", self.bit_width);
        }
    }

    pub fn mul(mut self, other: &Self,
               cs: &mut impl ConstraintSystem<E>,
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
        let product_lc = LinearCombination::<E>::zero() + product;

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

    pub fn equals_zero<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Boolean {
        let is_zero = {
            let value = self.value.map(|val| val.is_zero());
            Boolean::from(AllocatedBit::alloc::<E, &mut CS>(
                cs, value).unwrap())
        };
        let is_zero_lc = boolean_lc::<E, CS>(&is_zero);

        cs.enforce(
            || "eq=1 => self=0",
            |lc| lc + &self.lc,
            |lc| lc + &is_zero_lc,
            |lc| lc,
        );

        let self_inv = cs.alloc(
            || "inv",
            || Ok(
                self.value.unwrap().inverse()
                    .unwrap_or_else(|| E::Fr::zero())
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

    pub fn power_of_two<CS: ConstraintSystem<E>>(
        n: usize) -> Self
    {
        // Set a bit in a little-endian representation.
        let which_limb = n / 64;
        let which_bit = n % 64;
        let element = {
            let mut repr = <E::Fr as PrimeField>::Repr::default();
            let limbs: &mut [u64] = repr.as_mut();
            limbs[which_limb] |= 1 << which_bit;
            E::Fr::from_repr(repr).unwrap()
        };

        Num::<E> {
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

impl<'a, E: Engine> Add<&'a Num<E>> for Num<E> {
    type Output = Num<E>;

    fn add(mut self, other: &'a Num<E>) -> Num<E> {
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

impl<'a, E: Engine> Sub<&'a Num<E>> for Num<E> {
    type Output = Num<E>;

    fn sub(mut self, other: &'a Num<E>) -> Num<E> {
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


pub fn boolean_lc<E: Engine, CS: ConstraintSystem<E>>(
    bool: &Boolean,
) -> LinearCombination<E> {
    bool.lc(CS::one(), E::Fr::one())
}
