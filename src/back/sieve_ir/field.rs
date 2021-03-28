use ff::{Field,PrimeField};
use std::io::Write;

// 2**128 - 159
#[derive(PrimeField)]
#[PrimeFieldModulus = "340282366920938463463374607431768211297"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
pub struct QuarkScalar([u64; 3]);

/// Convert bellman Fr to zkInterface little-endian bytes.
/// TODO: Verify that Scalar::Repr is little-endian (not guaranteed by the API).
pub fn write_scalar<Scalar: PrimeField>(
    fr: &Scalar,
    writer: &mut impl Write,
) {
    let repr = fr.to_repr();
    writer.write_all(repr.as_ref()).unwrap();
}

pub fn encode_scalar<Scalar: PrimeField>(
    fr: &Scalar,
) -> Vec<u8> {
    let mut le = Vec::new();
    write_scalar(fr, &mut le);
    le
}
