use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::*;
use std::{io::Write, u8};

// 2**128 - 159
#[derive(PrimeField)]
#[PrimeFieldModulus = "340282366920938463463374607431768211297"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
pub struct QuarkScalar([u64; 3]);

/// Convert bellman Fr to zkInterface little-endian bytes.
/// TODO: Verify that Scalar::Repr is little-endian (not guaranteed by the API).
pub fn write_scalar<Scalar: PrimeField>(fr: &Scalar, writer: &mut impl Write) {
    let repr = fr.to_repr();
    writer.write_all(repr.as_ref()).unwrap();
}

pub fn encode_scalar<Scalar: PrimeField>(fr: &Scalar) -> Vec<u8> {
    let mut le = Vec::new();
    write_scalar(fr, &mut le);
    le
}

pub fn encode_field_order<Scalar: PrimeField>() -> Vec<u8> {
    let neg_one = Scalar::one().neg();
    let neg_one = BigUint::from_bytes_le(&encode_scalar(&neg_one));
    let order: BigUint = neg_one + BigUint::one();
    order.to_bytes_le()
}

pub fn _scalar_from_unsigned<Scalar: PrimeField>(val: u64) -> Result<Scalar, String> {
    scalar_from_biguint(&BigUint::from(val))
}

pub fn scalar_from_biguint<Scalar: PrimeField>(val: &BigUint) -> Result<Scalar, String> {
    let bytes = val.to_bytes_le();
    let mut repr: Scalar::Repr = Default::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes);
    Scalar::from_repr(repr).ok_or_else(|| format!("uint {} out of range for Scalar", val))
}
