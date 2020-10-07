// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use zkinterface_bellman::{
    ff::{Field, PrimeField},
    bellman::{
        SynthesisError,
        ConstraintSystem,
        LinearCombination,
        gadgets::boolean::{Boolean, AllocatedBit},
    },
};
use super::{
    num::Num,
    bit_width::BitWidth,
};

/// The size of integer representations in bits.
const SIZE: usize = 64;

/// Represents an interpretation of SIZE `Boolean` objects as a
/// unsigned integer, or two-complement signed integer.
#[derive(Clone)]
pub struct Int64 {
    // Least significant bit first
    pub bits: Vec<Boolean>,
    pub value: Option<u64>,
}

impl Int64 {
    /// Construct a constant `Int64` from a `u64`
    pub fn constant(value: u64) -> Self
    {
        let mut bits = Vec::with_capacity(SIZE);

        let mut tmp = value;
        for _ in 0..SIZE {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        Int64 {
            bits: bits,
            value: Some(value),
        }
    }

    /// Allocate a `Int64` in the constraint system
    pub fn alloc<Scalar, CS>(
        mut cs: CS,
        value: Option<u64>,
    ) -> Result<Self, SynthesisError>
        where Scalar: PrimeField,
              CS: ConstraintSystem<Scalar>
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(SIZE);

                for _ in 0..SIZE {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            }
            None => vec![None; SIZE]
        };

        let bits = values.into_iter()
            .enumerate()
            .map(|(i, v)| {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("allocated bit {}", i)),
                    v,
                )?))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(Int64 {
            bits: bits,
            value: value,
        })
    }

    pub fn from_num<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        num: &Num<Scalar>,
    ) -> Int64 {
        let mut bits = num.alloc_bits(&mut cs);
        let expand_bit = match num.bit_width {
            // Unsigned numbers are padded with zeros.
            BitWidth::Max(_, false) => Boolean::Constant(false),
            // Signed numbers are padded by copying the sign bit.
            BitWidth::Max(_, true) => bits[bits.len() - 1].clone(),
            _ => unreachable!(),
        };
        bits.resize(SIZE, expand_bit);
        Self::from_bits(&bits)
    }

    pub fn from_boolean(bool: &Boolean) -> Int64 {
        let mut bits = Vec::with_capacity(SIZE);
        bits.push(bool.clone());
        bits.resize(SIZE, Boolean::constant(false));

        Int64 {
            bits,
            value: bool.get_value().map(|b| b as u64),
        }
    }

    pub fn is_negative(&self) -> &Boolean {
        // Interpret the most significant bit as "is negative".
        self.bits.last().unwrap()
    }

    pub fn is_positive_or_zero(&self) -> Boolean {
        self.is_negative().not()
    }

    /// Turns this `Int64` into its little-endian byte order representation.
    pub fn into_bits(&self) -> Vec<Boolean> {
        self.bits.clone()
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `Int64`.
    pub fn from_bits(bits: &[Boolean]) -> Self
    {
        assert_eq!(bits.len(), SIZE);

        let new_bits = bits.to_vec();

        let mut value = Some(0u64);
        for b in new_bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match b {
                &Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                }
                &Boolean::Is(ref b) => {
                    match b.get_value() {
                        Some(true) => { value.as_mut().map(|v| *v |= 1); }
                        Some(false) => {}
                        None => { value = None }
                    }
                }
                &Boolean::Not(ref b) => {
                    match b.get_value() {
                        Some(false) => { value.as_mut().map(|v| *v |= 1); }
                        Some(true) => {}
                        None => { value = None }
                    }
                }
            }
        }

        Int64 {
            value: value,
            bits: new_bits,
        }
    }

    pub fn shift_left(&self, by: usize) -> Self {
        let by = by % SIZE;

        let fill = Boolean::constant(false);

        let new_bits = Some(&fill).into_iter().cycle() // Generate zeros to insert.
            .take(by) // Take the least significant zeros.
            .chain(self.bits.iter()) // Append the bits to keep.
            .take(SIZE) // Truncate to SIZE bits.
            .cloned().collect();

        Int64 {
            bits: new_bits,
            value: self.value.map(|v| v << by as u64),
        }
    }

    pub fn shift_right(&self, by: usize) -> Self {
        let by = by % SIZE;

        let fill = Boolean::constant(false);

        let new_bits = self.bits
            .iter() // The bits are least significant first
            .skip(by) // Skip the bits that will be lost during the shift
            .chain(Some(&fill).into_iter().cycle()) // Rest will be zeros
            .take(SIZE) // Only SIZE bits needed!
            .cloned()
            .collect();

        Int64 {
            bits: new_bits,
            value: self.value.map(|v| v >> by as u64),
        }
    }

    /// XOR this `Int64` with another `Int64`
    pub fn xor<Scalar, CS>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
        where Scalar: PrimeField,
              CS: ConstraintSystem<Scalar>
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => {
                Some(a ^ b)
            }
            _ => None
        };

        let bits = self.bits.iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| {
                Boolean::xor(
                    cs.namespace(|| format!("xor of bit {}", i)),
                    a,
                    b,
                )
            })
            .collect::<Result<_, _>>()?;

        Ok(Int64 {
            bits: bits,
            value: new_value,
        })
    }
}
