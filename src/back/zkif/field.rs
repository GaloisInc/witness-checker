use ff::PrimeField;

// 2**128 - 159
#[derive(PrimeField)]
#[PrimeFieldModulus = "340282366920938463463374607431768211297"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
pub struct QuarkScalar([u64; 3]);
