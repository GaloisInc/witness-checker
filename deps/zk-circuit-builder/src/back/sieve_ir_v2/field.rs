use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::*;
use std::{io::Write, u8};

// f128p field scalar declaration. To use this scalar type and prime
// value, enable the "f128p" Cargo feature.
#[cfg(feature = "f128p")]
mod scalar_f128p {
    use ff::PrimeField;

    // 2**128 - 159
    #[derive(PrimeField)]
    #[PrimeFieldModulus = "340282366920938463463374607431768211297"]
    #[PrimeFieldGenerator = "7"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct QuarkScalar([u64; 3]);
}

// f384p field scalar declaration. To use this scalar type and prime
// value, enable the "f384p" Cargo feature.
#[cfg(feature = "f384p")]
mod scalar_f384p {
    use ff::PrimeField;

    // The finite field over the prime
    // $`P = 2^{384} - 2^{128} - 2^{96} + 2^{32} - 1
    //     = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
    #[derive(PrimeField)]
    #[PrimeFieldModulus = "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319"]
    #[PrimeFieldGenerator = "19"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct QuarkScalar([u64; 7]);
}

#[cfg(feature = "f128p")] pub use self::scalar_f128p::QuarkScalar;
#[cfg(feature = "f384p")] pub use self::scalar_f384p::QuarkScalar;

/// Convert bellman Fr to zkInterface little-endian bytes.
pub fn write_scalar<Scalar: PrimeField>(fr: &Scalar, writer: &mut impl Write) {
    let repr = fr.to_repr();
    writer.write_all(repr.as_ref()).unwrap();
}

pub fn encode_scalar<Scalar: PrimeField>(fr: &Scalar) -> Vec<u8> {
    let mut le = Vec::new();
    write_scalar(fr, &mut le);
    le
}

pub fn get_field_order<Scalar: PrimeField>() -> BigUint {
    let neg_one = Scalar::one().neg();
    let neg_one = BigUint::from_bytes_le(&encode_scalar(&neg_one));
    neg_one + BigUint::one()
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

#[test]
fn test_backend_scalar() {
    // Test the scalar currently configured in the backend.
    use super::backend::Scalar;

    // Check the byte order of the Scalar encoding.
    use ff::Field;
    let repr = encode_scalar(&Scalar::one());
    assert_eq!(
        repr,
        vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    );

    // Check that the Scalar can fit the product of two 64 bits integers.
    // This does not mean it can hold the full 128 bits, but only the greatest product.
    let half_capacity = Scalar::NUM_BITS / 2;
    assert!(half_capacity >= 64);
    assert!(Scalar::CAPACITY >= 64);
    let max = BigUint::from(2u8).pow(half_capacity) - BigUint::from(1u8);
    let square = &max * &max;
    let square_scalar = scalar_from_biguint::<Scalar>(&square).unwrap();
    let square_re = BigUint::from_bytes_le(&encode_scalar(&square_scalar));
    assert_eq!(square, square_re);
}
