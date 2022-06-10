// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use std::cmp;
use num_bigint::BigUint;
use num_traits::Zero;

use zkinterface_bellman::{
    ff::PrimeField,
    bellman::{
        SynthesisError,
        ConstraintSystem,
        gadgets::boolean::{Boolean, AllocatedBit},
    },
};
use super::num::Num;

/// Represents an interpretation of SIZE `Boolean` objects as a
/// unsigned integer, or two-complement signed integer.
#[derive(Clone)]
pub struct Int {
    /// Least significant bit first.
    pub bits: Vec<Boolean>,
    /// The value, if known.
    ///
    /// Invariant: if `value` is `Some(x)`, then `x.bits() <= self.bits.len()`.
    pub value: Option<BigUint>,
}

impl Int {
    pub fn width(&self) -> usize {
        self.bits.len()
    }

    /// Construct a constant `Int` from a `BigUint`
    pub fn constant(width: usize, value: BigUint) -> Self
    {
        let mut bits = Vec::with_capacity(width);

        let digits = value.to_u32_digits();
        for i in 0..width {
            let idx = i / 32;
            let off = i % 32;
            let set = digits[idx] & (1 << off) != 0;
            bits.push(Boolean::constant(set))
        }

        Int {
            bits: bits,
            value: Some(value),
        }
    }

    /// Allocate an `Int` in the constraint system
    pub fn alloc<Scalar, CS>(
        mut cs: CS,
        width: usize,
        value: Option<BigUint>,
    ) -> Result<Self, SynthesisError>
        where Scalar: PrimeField,
              CS: ConstraintSystem<Scalar>
    {
        let values = match value {
            Some(ref val) => {
                let mut v = Vec::with_capacity(width);

                let digits = val.to_u32_digits();
                for i in 0..width {
                    let idx = i / 32;
                    let off = i % 32;
                    let digit = digits.get(idx).cloned().unwrap_or(0);
                    let set = digit & (1 << off) != 0;
                    v.push(Some(set));
                }

                v
            }
            None => vec![None; width]
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

        Ok(Int {
            bits: bits,
            value: value,
        })
    }

    pub fn from_num<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        width: usize,
        num: &Num<Scalar>,
    ) -> Int {
        // `alloc_bits` produces `num.real_bits` bits, but we only care about the valid ones.
        let mut bits = num.alloc_bits(&mut cs);
        bits.truncate(cmp::min(width, num.valid_bits as usize));

        if (num.valid_bits as usize) < width {
            eprintln!(
                "warning: bogus conversion from {}-valid-bit Num to {}-bit Int",
                num.valid_bits, width,
            );
            bits.resize(width, Boolean::Constant(false));
        }

        Self::from_bits(&bits)
    }

    pub fn is_negative(&self) -> &Boolean {
        // Interpret the most significant bit as "is negative".
        self.bits.last().unwrap()
    }

    pub fn is_positive_or_zero(&self) -> Boolean {
        self.is_negative().not()
    }

    /// Turns this `Int` into its little-endian byte order representation.
    pub fn into_bits(&self) -> Vec<Boolean> {
        self.bits.clone()
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `Int`.
    pub fn from_bits(bits: &[Boolean]) -> Self
    {
        let new_bits = bits.to_vec();

        let mut digits = Some(vec![0_u32; (bits.len() + 31) / 32]);
        for (i, b) in new_bits.iter().enumerate() {
            let idx = i / 32;
            let off = i % 32;
            match b {
                &Boolean::Constant(b) => {
                    if b {
                        digits.as_mut().map(|ds| { ds[idx] |= 1 << off; });
                    }
                }
                &Boolean::Is(ref b) => {
                    match b.get_value() {
                        Some(true) => { digits.as_mut().map(|ds| { ds[idx] |= 1 << off; }); }
                        Some(false) => {}
                        None => { digits = None }
                    }
                }
                &Boolean::Not(ref b) => {
                    match b.get_value() {
                        Some(false) => { digits.as_mut().map(|ds| { ds[idx] |= 1 << off; }); }
                        Some(true) => {}
                        None => { digits = None }
                    }
                }
            }
        }

        Int {
            value: digits.as_ref().map(|ds| BigUint::from_slice(ds)),
            bits: new_bits,
        }
    }

    pub fn shift_left(&self, by: usize) -> Self {
        let width = self.width();
        let by = by % width;

        let fill = Boolean::constant(false);

        let new_bits = Some(&fill).into_iter().cycle() // Generate zeros to insert.
            .take(by) // Take the least significant zeros.
            .chain(self.bits.iter()) // Append the bits to keep.
            .take(width) // Truncate to SIZE bits.
            .cloned().collect::<Vec<_>>();

        Int {
            bits: new_bits,
            value: self.value.as_ref().map(|v| {
                let mask = (BigUint::from(1_u8) << width) - 1_u8;
                (v << by) & mask
            }),
        }
    }

    pub fn shift_right(&self, by: usize, signed: bool) -> Self {
        let width = self.width();
        let by = by % width;

        let fill = if signed {
            self.bits.last().unwrap().clone()
        } else {
            Boolean::constant(false)
        };

        let new_bits = self.bits
            .iter() // The bits are least significant first
            .skip(by) // Skip the bits that will be lost during the shift
            .chain(Some(&fill).into_iter().cycle()) // Rest will be zeros
            .take(width) // Only SIZE bits needed!
            .cloned()
            .collect::<Vec<_>>();


        let value = match self.value.as_ref() {
            Some(v) => {
                let mut new_v = v >> by;
                if signed {
                    if !(v & (BigUint::from(1_u8) << (width - 1))).is_zero() {
                        new_v |= ((BigUint::from(1_u8) << by) - 1_u8) << (width - by);
                    }
                }
                Some(new_v)
            },
            None => None,
        };

        Int {
            bits: new_bits,
            value,
        }
    }

    /// XOR this `Int` with another `Int`
    pub fn xor<Scalar, CS>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
        where Scalar: PrimeField,
              CS: ConstraintSystem<Scalar>
    {
        let new_value = match (self.value.as_ref(), other.value.as_ref()) {
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

        Ok(Int {
            bits: bits,
            value: new_value,
        })
    }
}
