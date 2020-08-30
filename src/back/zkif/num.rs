// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use zkinterface_bellman::{
    ff::{ScalarEngine, Field, PrimeField},
    bellman::LinearCombination,
};
use std::ops::{Add, Sub, Mul};
use zkinterface_bellman::bellman::{ConstraintSystem, SynthesisError, Variable};
use zkinterface_bellman::sapling_crypto::circuit::boolean::{Boolean, AllocatedBit};
use zkinterface_bellman::pairing::Engine;
use zkinterface_bellman::ff::PrimeFieldRepr;
use crate::back::zkif::zkif_cs::{En, Fr, LC, ZkifCS, fr_from_signed, fr_from_unsigned};
use crate::back::zkif::bit_width::BitWidth;
use crate::back::zkif::uint32::UInt32;


#[derive(Clone)]
pub struct Num<E: Engine> {
    pub value: Option<E::Fr>,
    pub lc: LinearCombination<E>,
    /// How many bits would be required to represent this number.
    pub bit_width: BitWidth,
}

impl From<u64> for Num<En> {
    fn from(literal: u64) -> Self {
        let f: Fr = fr_from_unsigned(literal);
        Num {
            value: Some(f.clone()),
            lc: LC::zero() + (f, ZkifCS::one()),
            bit_width: BitWidth::from(literal),
        }
    }
}

impl From<i64> for Num<En> {
    fn from(literal: i64) -> Self {
        let f: Fr = fr_from_signed(literal);
        Num {
            value: Some(f.clone()),
            lc: LC::zero() + (f, ZkifCS::one()),
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

    pub fn alloc<CS: ConstraintSystem<E>>(
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

    pub fn from_uint<CS: ConstraintSystem<E>>(
        int: &UInt32,
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

    pub fn alloc_bits<CS: ConstraintSystem<E>>(
        &self, mut cs: CS) -> Vec<Boolean>
    {
        let (n_bits, signed) = match self.bit_width {
            BitWidth::Unknown => panic!("Cannot decompose a number of unknown size."),
            BitWidth::Max(n_bits, signed) => (n_bits, signed),
        };

        let values = match &self.value {
            Some(val) => {
                // TODO: handle negative numbers.
                let repr = val.into_repr();
                let limbs: &[u64] = repr.as_ref();
                let mut bools = Vec::with_capacity(n_bits);

                for i in 0..n_bits {
                    let limb = limbs[i / 64];
                    let bit = (limb >> (i % 64)) & 1 == 1;
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

        if !signed {
            cs.enforce(
                || "bit decomposition",
                |zero| zero,
                |zero| zero,
                |_| lc - &self.lc,
            );
        } else {
            eprintln!("TODO: bit decomposition of signed integers.");
        }
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
