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
    // TODO: this can probably be optimized
    let c_inv = sink.not(TEMP, 1, c);

    let c_mask = sink.concat_chunks(TEMP, &[(Source::RepWire(c), n)]);
    let c_inv_mask = sink.concat_chunks(TEMP, &[(Source::RepWire(c_inv), n)]);

    let t_masked = sink.and(TEMP, n, t, c_mask);
    let e_masked = sink.and(TEMP, n, e, c_inv_mask);

    sink.xor(expire, n, t_masked, e_masked)
}
