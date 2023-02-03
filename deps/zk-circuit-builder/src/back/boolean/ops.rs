use crate::ir::circuit::Bits;
use super::{WireId, Time, TEMP, Sink, Source, AssertNoWrap};


/// Generate a mux operation, which returns the value of `t` ("then") if `c` ("cond") is 1 and
/// returns `e` ("else") otherwise.  `c` is a 1-bit input, `t` and `e` are both `n`-bit inputs, and
/// the output is also `n` bits.
pub fn mux(
    sink: &mut impl Sink,
    expire: Time,
    n: u64,
    c: WireId,
    t: WireId,
    e: WireId,
) -> WireId {
    // `((t ^ e) & c) ^ e`.  When `c` is zero, this is `0 ^ e`;  otherwise, this is `t ^ e ^ e`.
    let c_mask = sink.concat_chunks(TEMP, &[(Source::RepWire(c), n)]);
    let te = sink.xor(TEMP, n, t, e);
    let te_masked = sink.and(TEMP, n, te, c_mask);
    sink.xor(expire, n, e, te_masked)
}
