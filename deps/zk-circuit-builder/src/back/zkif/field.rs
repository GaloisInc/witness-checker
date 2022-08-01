
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

#[cfg(feature = "f128p")] pub use self::scalar_f128p::QuarkScalar;
