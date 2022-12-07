use crate::ir::circuit::Bits;
use super::{WireId, Time, TEMP, Sink, Source};


fn add_common<S: Sink>(
    sink: &mut S,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
    c0: WireId,
) -> WireId {
    let a_xor_b = sink.xor(TEMP, n, a, b);
    let a_and_b = sink.and(TEMP, n, a, b);

    // Populate carries
    let mut carries = Vec::with_capacity(n as usize);
    let mut concat_parts = Vec::with_capacity(n as usize);
    carries.push(c0);
    concat_parts.push((Source::Wires(c0), 1));

    for i in 0 .. n - 1 {
        let c_in = *carries.last().unwrap();
        let and1 = a_and_b + i;
        let and2 = sink.and(TEMP, 1, a_xor_b + i, c_in);
        let c_out = sink.or(TEMP, 1, and1, and2);
        carries.push(c_out);
        concat_parts.push((Source::Wires(c_out), 1));
    }

    let c = sink.concat_chunks(TEMP, &concat_parts);
    sink.xor(expire, n, a_xor_b, c)
}

pub fn add(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    let c0 = sink.lit(TEMP, 1, Bits::zero());
    add_common(sink, expire, n, a, b, c0)
}

pub fn sub(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    let b_inv = sink.not(TEMP, n, b);
    let c0 = sink.lit(TEMP, 1, Bits::one());
    add_common(sink, expire, n, a, b_inv, c0)
}


/// Add `n`-bit input `a` to 1-bit input `b`, producing an `n`-bit result.
fn add_1(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    // This is like `add_common` where `b` is always zero and `c0` is the 1-bit input `b`.
    let a_xor_b = a;
    // `a_and_b` is all zeros.
    let c0 = b;

    // Populate carries
    let mut carries = Vec::with_capacity(n as usize);
    let mut concat_parts = Vec::with_capacity(n as usize);
    carries.push(c0);
    concat_parts.push((Source::Wires(c0), 1));

    for i in 0 .. n - 1 {
        let c_in = *carries.last().unwrap();
        // `and1 = a_and_b + i` is always zero.
        let and2 = sink.and(TEMP, 1, a_xor_b + i, c_in);
        let c_out = and2;
        carries.push(c_out);
        concat_parts.push((Source::Wires(c_out), 1));
    }

    let c = sink.concat_chunks(TEMP, &concat_parts);
    sink.xor(expire, n, a_xor_b, c)
}

pub fn neg(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
) -> WireId {
    let a_inv = sink.not(TEMP, n, a);
    let b = sink.lit(TEMP, 1, Bits::one());
    add_1(sink, expire, n, a_inv, b)
}


/// `Nx1 -> N` bit multiply.  Input `a` is `n` bits wide, and `b` is 1 bit wide.  The result is the
/// product `a * b`.
///
/// This is equivalent to `mux(b, a, 0)`.
fn mul_1(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    let b_ext = sink.concat_chunks(TEMP, &[(Source::RepWire(b), n)]);
    sink.and(expire, n, a, b_ext)
}

/// Zero-extend input `a` from `n` bits to `m` bits.
fn zero_extend(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    m: u64,
) -> WireId {
    if m < n {
        // We are truncating instead.
        return a;
    }
    sink.concat_chunks(expire, &[
        (Source::Wires(a), n),
        (Source::Zero, m - n),
    ])
}

/// Sign-extend input `a` from `n` bits to `m` bits.
fn sign_extend(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    m: u64,
) -> WireId {
    if m < n {
        // We are truncating instead.
        return a;
    }
    sink.concat_chunks(expire, &[
        (Source::Wires(a), n),
        (Source::RepWire(a + n - 1), m - n),
    ])
}

pub fn mul_simple(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    //      1111
    //    x 1111
    //    ------
    //      1111  <- acc[0], equal to row0 but extended to n+1 bits
    //      111   <- row1, shifted
    //      -----    Note acc[0] gets zero-extended by 1 for this addition (denoted by leading _)
    //      110 1 <- acc[1] + low_bits[0]
    //      11    <- row2, shifted
    //      -----
    //      10 01 <- acc[2] + low_bits[0..2]
    //      1
    //      -----
    //      0 001 <- acc[3] + low_bits[0..3]

    debug_assert!(n > 0);
    let mut acc = mul_1(sink, TEMP, n, a, b);

    let mut concat_parts = Vec::with_capacity(n as usize);
    for i in 1 .. n {
        let m = n - i;
        let row = mul_1(sink, TEMP, m, a, b + i);
        // We are computing the following addition:
        //       AAAAA   acc (m+1 bits)
        //    +  RRRR    row (m bits)
        //    --------
        //       BBBBA   new acc (m bits) plus low bit passed through (1 bit)
        //
        // Note that `row` is shifted past the low bit of `acc`, so the low bit is passed through
        // unmodified.  Also note that `acc` shrinks (`m` decreases) with each iteration.
        concat_parts.push((Source::Wires(acc), 1));

        acc = sink.add(TEMP, m, acc + 1, row);
    }

    // After the last iteration, `acc` is only one bit wide.
    concat_parts.push((Source::Wires(acc), 1));
    let out = sink.concat_chunks(expire, &concat_parts);
    out
}

pub fn wide_mul_simple(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    //      1111
    //    x 1111
    //    ------
    //    _01111  <- acc[0], equal to row0 but extended to n+1 bits
    //    01111   <- row1, shifted
    //    -------    Note acc[0] gets zero-extended by 1 for this addition (denoted by leading _)
    //   _10110 1 <- acc[1] + low_bits[0]
    //   01111    <- row2, shifted
    //   --------
    //  _11010 01 <- acc[2] + low_bits[0..2]
    //  01111
    //  ---------
    //  11100 001 <- acc[3] + low_bits[0..3]
    eprintln!("n = {}, a = {}, b = {}", n, a, b);

    debug_assert!(n > 0);
    let row0 = mul_1(sink, TEMP, n, a, b);
    let mut acc = sink.concat_chunks(TEMP, &[
        (Source::Wires(row0), n),
        (Source::Zero, 1),
    ]);

    let mut concat_parts = Vec::with_capacity(n as usize);
    for i in 1 .. n {
        let row = mul_1(sink, TEMP, n, a, b + i);
        // We are computing the following addition:
        //       AAAAA   acc (n+1 bits)
        //    +  RRRR    row (n bits)
        //    --------
        //      BBBBBA   new acc (n+1 bits) plus low bit passed through (1 bit)
        //
        // Note that `row` is shifted past the low bit of `acc`, so the low bit is passed through
        // unmodified.  Also note that the output is potentially `n + 1` bits wide, so we must
        // zero-extend both `row` and the `n` high bits of `acc` before adding.
        concat_parts.push((Source::Wires(acc), 1));

        let acc_ext = zero_extend(sink, TEMP, n, acc + 1, n + 1);
        let row_ext = zero_extend(sink, TEMP, n, row, n + 1);
        acc = sink.add(TEMP, n + 1, acc_ext, row_ext);
    }

    concat_parts.push((Source::Wires(acc), n + 1));
    let out = sink.concat_chunks(expire, &concat_parts);
    out
}

pub fn wide_mul_karatsuba(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    if n <= 1 {
        return sink.and(expire, n, a, b);
    }

    // https://en.wikipedia.org/wiki/Karatsuba_algorithm
    // We use the variable names from that writeup, with inputs `x` and `y` rather than `a` and
    // `b`.
    let x = a;
    let y = b;

    let m = (n + 1) / 2;

    let x0 = x;
    let y0 = y;
    let (x1, y1) = if n % 2 == 0 {
        (x + m, y + m)
    } else {
        // Zero-extend from `m - 1` bits to `m` bits.
        (
            zero_extend(sink, TEMP, m - 1, x + m, m),
            zero_extend(sink, TEMP, m - 1, y + m, m),
        )
    };

    let z2 = sink.wide_mul(TEMP, m, x1, y1);
    let z0 = sink.wide_mul(TEMP, m, x0, y0);

    // TODO: this could be optimized with shifted and implicitly-extending add operations
    let x0_ext = zero_extend(sink, TEMP, m, x0, m + 1);
    let x1_ext = zero_extend(sink, TEMP, m, x1, m + 1);
    let y0_ext = zero_extend(sink, TEMP, m, y0, m + 1);
    let y1_ext = zero_extend(sink, TEMP, m, y1, m + 1);
    let x0x1 = sink.add(TEMP, m + 1, x0_ext, x1_ext);
    let y0y1 = sink.add(TEMP, m + 1, y0_ext, y1_ext);
    let z1_product = sink.wide_mul(TEMP, m + 1, x0x1, y0y1);
    let z0_ext = zero_extend(sink, TEMP, m * 2, z0, (m + 1) * 2);
    let z2_ext = zero_extend(sink, TEMP, m * 2, z2, (m + 1) * 2);
    let z0z2_ext = sink.add(TEMP, (m + 1) * 2, z0_ext, z2_ext);
    let z1 = sink.sub(TEMP, (m + 1) * 2, z1_product, z0z2_ext);

    // Low `m` bits of output are the lowest `m` bits of `z0`.
    let low = z0;

    // Middle `m` bits are the sum of `z0 >> m` and `z1`.
    let mid = {
        let a_ext = zero_extend(sink, TEMP, m, z0 + m, 2 * m + 3);
        let b_ext = zero_extend(sink, TEMP, (m + 1) * 2, z1, 2 * m + 3);
        sink.add(TEMP, 2 * m + 3, a_ext, b_ext)
    };

    // High `2 * m` bits are the sum of `mid >> m` and `z2`.
    let high = {
        let a_ext = zero_extend(sink, TEMP, m + 3, mid + m, 2 * m);
        sink.add(TEMP, 2 * m, a_ext, z2)
    };

    sink.concat_chunks(expire, &[
        (Source::Wires(low), m),
        (Source::Wires(mid), m),
        (Source::Wires(high), 2 * m),
    ])
}

pub fn wide_mul(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    // Empirically, the Karatsuba multiplier uses fewer AND gates than the simple multiplier when
    // `n` is 18, 20, 22, or 24+.
    //
    // To find the right values of `n` to accept here, first, modify the test
    // `wide_mul_karatsuba_performance` (in `boolean/mod.rs`) to check all values of `n` in the
    // range `1 ..= 64`.  Then, adjust the condition here until it accepts as many values of `n` as
    // possible without causing the test to fail.
    if n < 18 || (n < 24 && n % 2 == 1) {
        wide_mul_simple(sink, expire, n, a, b)
    } else {
        wide_mul_karatsuba(sink, expire, n, a, b)
    }
}

