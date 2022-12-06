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
