// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use std::cmp;
use std::ops::{Add, Sub, Mul, AddAssign};
use num_bigint::BigUint;

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

    /// Conservative upper bound on the number of bits required to represent this number.
    /// Specifically, the `Scalar` value is always less than `2^real_bits`.  `real_bits` may exceed
    /// `logical_bits`, but can't exceed the size of the field.
    pub real_bits: u16,

    /// The number of bits containing meaningful values.  Bits in the range `valid_bits ..
    /// real_bits` may contain arbitrary data.
    pub valid_bits: u16,
}

impl<Scalar: PrimeField> Num<Scalar> {
    pub fn from_biguint(
        width: u16,
        value: &BigUint,
    ) -> Num<Scalar> {
        let element: Scalar = scalar_from_biguint(value);
        Num {
            value: Some(element.clone()),
            lc: LinearCombination::zero() + (element, ZkifCS::<Scalar>::one()),
            real_bits: width,
            valid_bits: width,
        }
    }

    pub fn _alloc<CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        width: u16,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError>
    {
        let value = value.map(|val| scalar_from_biguint(&val));
        let var = cs.alloc(|| "num", ||
            value.ok_or(SynthesisError::AssignmentMissing))?;
        Ok(Num {
            value,
            lc: LinearCombination::zero() + var,
            real_bits: width,
            valid_bits: width,
        })
    }

    pub fn from_int<CS: ConstraintSystem<Scalar>>(
        int: &Int,
    ) -> Num<Scalar> {
        let value = int.value.as_ref().map(scalar_from_biguint);
        let lc = Self::lc_from_bits::<CS>(&int.bits);
        let width = int.width() as u16;

        Num {
            value,
            lc,
            real_bits: width,
            valid_bits: width,
        }
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

    /// Decompose this number into bits, least-significant first.  Returns `self.real_bits` bits.
    pub fn alloc_bits<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
    ) -> Vec<Boolean> {
        let n_bits = self.real_bits as usize;

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

    // TODO: Turn add/sub/mul/neg into wrappers that check for the necessary width and truncate the
    // inputs to `cmp::min(self.real_bits, other.real_bits)` if needed.

    pub fn add(
        mut self,
        other: &Self,
        // `cs` argument will be needed when we add automatic truncation
        _cs: &mut impl ConstraintSystem<Scalar>,
    ) -> Self {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.add_assign(other_val),
            _ => {}
        }

        self.lc = self.lc + &other.lc;
        let new_real_bits = cmp::max(self.real_bits, other.real_bits) + 1;
        assert!(
            new_real_bits <= Scalar::CAPACITY as u16,
            "sum of {} bits and {} bits doesn't fit in a field element ({} bits)",
            self.real_bits, other.real_bits, Scalar::CAPACITY,
        );
        self.real_bits = new_real_bits;
        self.valid_bits = cmp::min(self.valid_bits, other.valid_bits);
        self
    }

    pub fn sub(
        mut self,
        other: &Self,
        _cs: &mut impl ConstraintSystem<Scalar>,
    ) -> Self {
        // `a - b` might underflow in the field, producing garbage.  We compute `a + (2^N - b)`
        // instead, with `N` large enough that `2^N - b` can't underflow.  This makes `a.sub(b)`
        // essentially equivalent to `a.add(b.neg())`, except it saves a bit.  `2^N - b` is at most
        // `2^N`, and the sum `a + 2^N` is at most `1 + max(a_bits, N)` bits, so `sub` adds 1 bit
        // to the size of its inputs.  But `neg` and `add` would each add 1, for a total of 2.
        //
        // Note we don't need to consult `self.real_bits` here.  If `self.real_bits >
        // other.real_bits`, then we'll trample on some high bits of `self`, but that's okay
        // because `valid_bits` is the `min` of the two inputs, and will be smaller than
        // `other.real_bits`.
        let max_value = scalar_from_biguint(&(BigUint::from(1_u8) << other.real_bits));

        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.add_assign(max_value - other_val),
            _ => {}
        }

        self.lc = self.lc + (max_value, ZkifCS::<Scalar>::one()) - &other.lc;

        let new_real_bits = cmp::max(self.real_bits, other.real_bits) + 1;
        assert!(
            new_real_bits <= Scalar::CAPACITY as u16,
            "sum of {} bits and {} bits doesn't fit in a field element ({} bits)",
            self.real_bits, other.real_bits, Scalar::CAPACITY,
        );
        self.real_bits = new_real_bits;
        self.valid_bits = cmp::min(self.valid_bits, other.valid_bits);
        self
    }

    pub fn mul(
        mut self,
        other: &Self,
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

        fn mul_bits(b1: u16, b2: u16) -> u16 {
            // If `bits == 0`, then the value must be zero, so the product is also zero.
            if b1 == 0 || b2 == 0 { 0 }
            // If `bits == 1`, then the value must be 0 or 1.  The product can either be zero or
            // the value of the other input.
            else if b1 == 1 { b2 }
            else if b2 == 1 { b1 }
            else { b1 + b2 }
        }
        let new_real_bits = mul_bits(self.real_bits, other.real_bits);
        // NB: This is the one case where `real_bits` is allowed to exactly equal the number of
        // bits in a field element.  The inputs can't exceed `2^b1 - 1` and `2^b2 - 1`, so the
        // product will be less than `2^(b1 + b2)` by at least `2^b1 + 2^b2`; in the worst case
        // (`b1 = b2 = CAPACITY / 2`), this is a fairly large number, like `2^64`.  We assume the
        // prime modulus is much closer to `2^CAPACITY` than that, so the product will fit.
        // FIXME: Check the assumption that the prime modulus is `>= 2^CAPACITY - 2^(CAPACITY/2)`.
        assert!(
            new_real_bits <= Scalar::CAPACITY as u16,
            "product of {} bits and {} bits doesn't fit in a field element ({} bits)",
            self.real_bits, other.real_bits, Scalar::CAPACITY,
        );
        self.real_bits = new_real_bits;

        self.valid_bits = cmp::min(self.real_bits, other.real_bits);
        assert!(self.valid_bits <= self.real_bits);

        self
    }

    pub fn neg(
        mut self,
        _cs: &mut impl ConstraintSystem<Scalar>,
    ) -> Self {
        // Computing `0 - a` in the field could underflow, producing garbage.  We instead compute
        // `2^N - a`, which never underflows, but does increase `real_bits` by one.
        let max_value = scalar_from_biguint(&(BigUint::from(1_u8) << self.real_bits));

        self.value = match self.value {
            Some(val) => Some(max_value - val),
            None => None,
        };

        self.lc = LinearCombination::zero() + (max_value, ZkifCS::<Scalar>::one()) - &self.lc;

        let new_real_bits = self.real_bits + 1;
        assert!(
            new_real_bits <= Scalar::CAPACITY as u16,
            "negation of {} bits doesn't fit in a field element ({} bits)",
            self.real_bits, Scalar::CAPACITY,
        );
        self.real_bits = new_real_bits;
        // `valid_bits` remains the same.
        self
    }

    /// Truncate `self` modulo `2^valid_bits`, producing a new `Num` with `real_bits ==
    /// valid_bits`.
    pub fn truncate<CS: ConstraintSystem<Scalar>>(
        mut self,
        cs: &mut CS,
    ) -> Self {
        if self.real_bits == self.valid_bits {
            return self;
        }

        let int = Int::from_num(cs, self.valid_bits as usize, &self);
        Self::from_int::<CS>(&int)
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
}


pub fn boolean_lc<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    bool: &Boolean,
) -> LinearCombination<Scalar> {
    bool.lc(CS::one(), Scalar::one())
}


pub fn scalar_from_unsigned<Scalar: PrimeField>(val: u64) -> Scalar {
    scalar_from_biguint(&BigUint::from(val))
}

pub fn scalar_from_biguint<Scalar: PrimeField>(val: &BigUint) -> Scalar {
    let bytes = val.to_bytes_le();
    let mut repr: Scalar::Repr = Default::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes);
    Scalar::from_repr(repr)
        .expect("uint out of range for Scalar")
}
