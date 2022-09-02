
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

    #[derive(PrimeField)]
    #[PrimeFieldModulus = "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319"]
    #[PrimeFieldGenerator = "19"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct QuarkScalar([u64; 7]);
}

#[cfg(feature = "f128p")] pub use self::scalar_f128p::QuarkScalar;
#[cfg(feature = "f384p")] pub use self::scalar_f384p::QuarkScalar;
