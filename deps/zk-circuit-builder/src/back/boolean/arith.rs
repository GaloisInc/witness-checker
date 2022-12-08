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
    assert!(n >= 4);

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

    use log::trace;
    trace!("x = {}", x);
    trace!("y = {}", y);
    trace!("x0 = {}", x0);
    trace!("x1 = {}", x1);
    trace!("y0 = {}", y0);
    trace!("y1 = {}", y1);
    trace!("x0x1 = {}", x0x1);
    trace!("y0y1 = {}", y0y1);
    trace!("z1_product = {}", z1_product);
    trace!("z0z2_ext = {}", z0z2_ext);
    trace!("z0 = {}", z0);
    trace!("z1 = {}", z1);
    trace!("z2 = {}", z2);
    trace!("low = {}", low);
    trace!("mid = {}", mid);
    trace!("high = {}", high);

    let out = sink.concat_chunks(expire, &[
        (Source::Wires(low), m),
        (Source::Wires(mid), m),
        (Source::Wires(high), 2 * m),
    ]);
    trace!("out = {}", out);
    out
}

pub fn mul_karatsuba(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    assert!(n >= 4);

    // This is structured similarly to `wide_mul_karatsuba`, but since we only require `n` bits of
    // the output instead of `2 * n` bits, we can omit `z2` and use the simpler formula for `z1`:
    //
    //      z1 = x1 * y0 + x0 * y1
    //
    // This still uses only 3 recursive multiplies, but saves some additions.

    // We still use the variable names from the "Karatsuba algorithm" Wikipedia page, with inputs
    // `x` and `y` rather than `a` and `b`, even though we aren't actually using the actual
    // Karatsuba algorithm.
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

    let z0 = sink.wide_mul(TEMP, m, x0, y0);

    // Since the final sum uses only the lowest `m` bits of `z1`, we can truncate here to save
    // adds.
    let x0y1 = sink.mul(TEMP, m, x0, y1);
    let x1y0 = sink.mul(TEMP, m, x1, y0);
    let z1 = sink.add(TEMP, m, x0y1, x1y0);

    // Low `m` bits of output are the lowest `m` bits of `z0`.
    let low = z0;

    // Middle `m` bits are the sum of `z0 >> m` and `z1`.
    let mid = sink.add(TEMP, m, z0 + m, z1);

    use log::trace;
    trace!("x = {}", x);
    trace!("y = {}", y);
    trace!("x0 = {}", x0);
    trace!("x1 = {}", x1);
    trace!("y0 = {}", y0);
    trace!("y1 = {}", y1);
    trace!("x0y1 = {}", x0y1);
    trace!("x1y0 = {}", x1y0);
    trace!("z0 = {}", z0);
    trace!("z1 = {}", z1);
    trace!("low = {}", low);
    trace!("mid = {}", mid);

    let out = sink.concat_chunks(expire, &[
        (Source::Wires(low), m),
        (Source::Wires(mid), m),
    ]);
    trace!("out = {}", out);
    out
}


fn wide_mul_use_karatsuba(n: u64) -> bool {
    match n {
        18 | 20 | 22 => true,
        _ => n >= 24,
    }
}

pub fn wide_mul(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    if !wide_mul_use_karatsuba(n) {
        wide_mul_simple(sink, expire, n, a, b)
    } else {
        wide_mul_karatsuba(sink, expire, n, a, b)
    }
}

fn mul_use_karatsuba(n: u64) -> bool {
    match n {
        44 | 48 | 52 | 56 |
        58 | 59 | 60 |
        62 | 63 | 64 |
        66 | 67 | 68 => true,
        _ => n >= 70,
    }
}

pub fn mul(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    a: WireId,
    b: WireId,
) -> WireId {
    if !mul_use_karatsuba(n) {
        mul_simple(sink, expire, n, a, b)
    } else {
        mul_karatsuba(sink, expire, n, a, b)
    }
}


#[cfg(test)]
mod test {
    use num_bigint::BigUint;
    use crate::ir::circuit::Bits;
    use crate::back::boolean::{Time, WireId, TEMP, Source, Sink};
    use crate::back::boolean::arith;
    use crate::back::boolean::test::{TestSink, TestArithSink};

    /// Compute which sizes of multipliers are better done with the Karatsuba algorithm rather than
    /// the simple algorithm, then check that the `mul_use_karatsuba` functions implement the right
    /// check.
    #[test]
    fn karatsuba_performance() {
        let mut sink = TestArithSink::default();

        const MAX: u64 = 64;
        let a = sink.private(TEMP, MAX, Some(Bits::zero()));
        let b = sink.private(TEMP, MAX, Some(Bits::zero()));

        // The Karatsuba algorithm is not usable for `n < 4` (it would recurse infinitely).
        for n in 4 ..= MAX {
            // Test wide_mul
            let before = sink.inner.count_and;
            let _ = arith::wide_mul_karatsuba(&mut sink, TEMP, n, a, b);
            let count_karatsuba = sink.inner.count_and - before;

            let before = sink.inner.count_and;
            let _ = arith::wide_mul_simple(&mut sink, TEMP, n, a, b);
            let count_simple = sink.inner.count_and - before;

            eprintln!("wide_mul({}): use {} ({} vs {})",
                n, if count_karatsuba < count_simple { "karatsuba" } else { "simple" },
                count_karatsuba, count_simple);

            if count_karatsuba < count_simple {
                // On future iterations, use the Karatsuba algorithm for any recursive calls of
                // size `n`.
                sink.use_karatsuba_sizes_wide.insert(n);
            }

            // Test mul
            let before = sink.inner.count_and;
            let _ = arith::mul_karatsuba(&mut sink, TEMP, n, a, b);
            let count_karatsuba = sink.inner.count_and - before;

            let before = sink.inner.count_and;
            let _ = arith::mul_simple(&mut sink, TEMP, n, a, b);
            let count_simple = sink.inner.count_and - before;

            if count_karatsuba < count_simple {
                sink.use_karatsuba_sizes.insert(n);
            }

            eprintln!("mul({}): use {} ({} vs {})",
                n, if count_karatsuba < count_simple { "karatsuba" } else { "simple" },
                count_karatsuba, count_simple);
        }

        let mut ok = true;
        for n in 4 ..= MAX {
            let expect = sink.use_karatsuba_sizes_wide.contains(&n);
            let actual = super::wide_mul_use_karatsuba(n);
            if expect != actual {
                eprintln!("expected wide_mul_use_karatsuba({}) = {}, but got {}",
                    n, expect, actual);
                ok = false;
            }

            let expect = sink.use_karatsuba_sizes.contains(&n);
            let actual = super::mul_use_karatsuba(n);
            if expect != actual {
                eprintln!("expected mul_use_karatsuba({}) = {}, but got {}",
                    n, expect, actual);
                ok = false;
            }
        }

        assert!(ok);
    }


    #[test]
    fn mul_karatsuba() {
        // We use `TestSink` so that recursive `mul`/`wide_mul` calls use the `BigInt`-based
        // multiplier.  This lets us test each size of Karatsuba multiplier in isolation.
        let mut sink = TestSink::default();

        for n in 4 ..= 5 {
            let mask = BigUint::from((1_u32 << n) - 1);
            for a_val in 0 .. 1 << n {
                let a = sink.lit(TEMP, n, Bits(&[a_val]));
                for b_val in 0 .. 1 << n {
                    let b = sink.lit(TEMP, n, Bits(&[b_val]));
                    let out = arith::mul_karatsuba(&mut sink, TEMP, n, a, b);
                    let out_val = sink.get_uint(n, out);
                    assert_eq!((BigUint::from(a_val) * BigUint::from(b_val)) & &mask, out_val,
                        "with n = {}, a_val = {}, b_val = {}", n, a_val, b_val);
                }
            }
        }
    }

    #[test]
    fn wide_mul_karatsuba() {
        // We use `TestSink` so that recursive `mul`/`wide_mul` calls use the `BigInt`-based
        // multiplier.  This lets us test each size of Karatsuba multiplier in isolation.
        let mut sink = TestSink::default();

        for n in 4 ..= 5 {
            for a_val in 0 .. 1 << n {
                let a = sink.lit(TEMP, n, Bits(&[a_val]));
                for b_val in 0 .. 1 << n {
                    let b = sink.lit(TEMP, n, Bits(&[b_val]));
                    let out = arith::wide_mul_karatsuba(&mut sink, TEMP, n, a, b);
                    let out_val = sink.get_uint(2 * n, out);
                    assert_eq!((BigUint::from(a_val) * BigUint::from(b_val)), out_val,
                        "with n = {}, a_val = {}, b_val = {}", n, a_val, b_val);
                }
            }
        }
    }
}
