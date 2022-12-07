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

        let acc_ext = sink.concat_chunks(TEMP, &[
            (Source::Wires(acc + 1), n),
            (Source::Zero, 1),
        ]);
        let row_ext = sink.concat_chunks(TEMP, &[
            (Source::Wires(row), n),
            (Source::Zero, 1),
        ]);
        acc = sink.add(TEMP, n + 1, acc_ext, row_ext);
    }

    concat_parts.push((Source::Wires(acc), n + 1));
    let out = sink.concat_chunks(expire, &concat_parts);
    out
}
