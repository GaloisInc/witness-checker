// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use zkinterface_bellman::{
    ff::{Field, PrimeField},
    pairing::Engine,
    bellman::{
        SynthesisError,
        ConstraintSystem,
        LinearCombination,
    },
    sapling_crypto::circuit::{
        boolean::{Boolean, AllocatedBit},
        multieq::MultiEq,
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
    pub fn alloc<E, CS>(
        mut cs: CS,
        value: Option<u64>,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
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

    pub fn from_num<E: Engine, CS: ConstraintSystem<E>>(
        mut cs: CS,
        num: &Num<E>,
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
    pub fn xor<E, CS>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
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

/*
#[cfg(test)]
mod test {
    use rand::{XorShiftRng, SeedableRng, Rng};
    use super::{Int64};
    use zkinterface_bellman::{
        bellman::ConstraintSystem,
        ff::Field,
        pairing::bls12_381::{Bls12},
        test_cs::TestConstraintSystem,
        sapling_crypto::circuit::{
            boolean::Boolean,
            multieq::MultiEq,
        },
    };

    #[test]
    fn test_uint64_from_bits() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let mut v = (0..SIZE).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();

            let b = Int64::from_bits(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match bit {
                    &Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    }
                    _ => unreachable!()
                }
            }

            let expected_to_be_same = b.into_bits();

            for x in v.iter().zip(expected_to_be_same.iter())
            {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                    _ => unreachable!()
                }
            }
        }
    }

    #[test]
    fn test_uint64_xor() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a: u64 = rng.gen();
            let b: u64 = rng.gen();
            let c: u64 = rng.gen();

            let mut expected = a ^ b ^ c;

            let a_bit = Int64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = Int64::constant(b);
            let c_bit = Int64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = a_bit.xor(cs.namespace(|| "first xor"), &b_bit).unwrap();
            let r = r.xor(cs.namespace(|| "second xor"), &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_shift_right() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..50 {
            for i in 0..60 {
                let num = rng.gen();
                let a = Int64::constant(num).shift_right(i);
                let b = Int64::constant(num >> i);

                assert_eq!(a.value.unwrap(), num >> i);

                assert_eq!(a.bits.len(), b.bits.len());
                for (a, b) in a.bits.iter().zip(b.bits.iter()) {
                    assert_eq!(a.get_value().unwrap(), b.get_value().unwrap());
                }
            }
        }
    }
}
*/