use std::cmp;
use std::collections::{BTreeMap, HashMap};
use std::num::Wrapping;
use arrayvec::ArrayVec;
use crate::eval::{self, CachingEvaluator};
use crate::gadget::bit_pack;
use crate::ir::circuit::{Wire, TyKind, CircuitTrait, CircuitExt, GateKind, UnOp, BinOp};
use crate::ir::typed::{TWire, Builder, EvaluatorExt};
use crate::micro_ram::types::{MemOpWidth, WORD_BYTES, WORD_LOG_BYTES, ByteOffset, MemSegment};

/// The known contents of memory at some point in the execution.  This is used to resolve some
/// memory loads to a wire containing the value without using an actual memory port.
#[derive(Clone, Debug, Default)]
pub struct KnownMem<'a> {
    mem: BTreeMap<u64, MemEntry<'a>>,
    default: Option<TWire<'a, u64>>,
    /// Address ranges where the `default` has been overwritten with unknown values.
    default_erased: RangeSet,

    /// Records the upper bound on the range of certain wires.
    wire_range: HashMap<TWire<'a, u64>, u64>,
}

#[derive(Clone, Debug)]
struct MemEntry<'a> {
    width: MemOpWidth,
    value: TWire<'a, u64>,
    /// This flag is `true` if any byte covered by this entry might be poisoned.  We conservatively
    /// refuse to resolve loads of possibly-poisoned bytes, so that the caller will instead use a
    /// normal `MemPort`, which can detect the poison if present.
    poisoned: bool,
}

impl<'a> KnownMem<'a> {
    // Note that most code in these functions works with *inclusive* ranges, not exclusive ones.
    // This helps avoid overflow for operations near the end of the address space: the inclusive
    // upper bound `0xfff...` (2^64 - 1) can be computed without overflow, but the exclusive bound
    // `0x1000...` (2^64) can't be represented in a 64-bit integer.

    pub fn new() -> KnownMem<'a> {
        KnownMem::default()
    }

    pub fn with_default(default: TWire<'a, u64>) -> KnownMem<'a> {
        KnownMem {
            default: Some(default),
            .. KnownMem::default()
        }
    }

    pub fn init_segment(
        &mut self,
        seg: &MemSegment,
        values: &[TWire<'a, u64>],
    ) {
        for i in 0 .. seg.len {
            let waddr = (seg.start + i) * WORD_BYTES as u64;
            let value = values[i as usize];
            self.mem.insert(waddr, MemEntry { width: MemOpWidth::WORD, value, poisoned: false });
        }
    }

    /// Indicate that the value of `wire` is publicly known to be in the range `0 ..= max`.
    pub fn set_wire_range(&mut self, wire: TWire<'a, u64>, max: u64) {
        self.wire_range.insert(wire, max);
    }

    pub fn load(
        &mut self,
        b: &Builder<'a>,
        ev: &mut CachingEvaluator<'a, '_, eval::Public>,
        addr: TWire<'a, u64>,
        width: MemOpWidth,
    ) -> Option<TWire<'a, u64>> {
        // Get the address being loaded as a `u64`.  If the address isn't a constant, then we can't
        // determine anything about the value.
        let public_addr = ev.eval_typed(addr)?;
        self.load_public(b, public_addr, width)
    }

    fn load_public(
        &mut self,
        b: &Builder<'a>,
        addr: u64,
        width: MemOpWidth,
    ) -> Option<TWire<'a, u64>> {
        assert!(addr % width.bytes() as u64 == 0);
        let end = end_addr(addr, width);
        let (waddr, _offset) = split_mem_addr(addr);

        let mut parts = ArrayVec::<[_; WORD_BYTES]>::new();
        // Total number of bytes among all the values in `parts`.
        let mut parts_bytes = 0;

        debug_assert!(end - waddr <= WORD_BYTES as u64);
        for (&mem_addr, entry) in self.mem.range(waddr ..= end) {
            let mem_end = end_addr(mem_addr, entry.width);
            if mem_end < addr {
                continue;
            }
            // Otherwise, this `mem` entry overlaps `addr ..= end`.

            if entry.poisoned {
                // Don't resolve loads that touch possibly-poisoned bytes.
                return None;
            }

            if entry.width >= width {
                // This entry covers the entire load.
                debug_assert!(parts.len() == 0);
                debug_assert!(mem_end >= end);
                let lo = addr - mem_addr;
                let hi = end - mem_addr + 1;
                return Some(extract_byte_range_extended(b, entry.value, lo, hi));
            } else {
                // This entry covers a strict subset of the load.

                if parts_bytes < mem_addr - addr {
                    // Add part of the default value.
                    let default = self.default?;
                    // No underflow: we know `mem_addr > 0` because `mem_addr - addr > 0`.
                    if self.default_erased(addr + parts_bytes, mem_addr - 1) {
                        return None;
                    }
                    let lo = addr + parts_bytes - waddr;
                    let hi = mem_addr - waddr;
                    let padding = extract_byte_range(b, default, lo, hi);
                    parts.push(padding);
                    parts_bytes += hi - lo;
                }

                let lo = addr + parts_bytes - mem_addr;
                let hi = mem_end - mem_addr + 1;
                let part = extract_byte_range(b, entry.value, lo, hi);
                parts.push(part);
                parts_bytes += hi - lo;
            }
        }

        if parts_bytes < width.bytes() as u64 {
            let default = self.default?;
            if self.default_erased(addr + parts_bytes, end) {
                return None;
            }
            let lo = addr + parts_bytes - waddr;
            let hi = end - waddr + 1;
            let padding = extract_byte_range(b, default, lo, hi);
            parts.push(padding);
        }

        let w = bit_pack::concat_bits_raw(b.circuit(), &parts);
        let w = b.circuit().cast(w, b.circuit().ty(TyKind::U64));
        Some(TWire::new(w))
    }

    /// Check whether the default value has been erased for any byte within the exclusive range
    /// `start ..= end`.
    fn default_erased(&self, start: u64, end: u64) -> bool {
        self.default_erased.overlaps(start, end)
    }

    pub fn store(
        &mut self,
        b: &Builder<'a>,
        ev: &mut CachingEvaluator<'a, '_, eval::Public>,
        addr: TWire<'a, u64>,
        value: TWire<'a, u64>,
        width: MemOpWidth,
    ) {
        self.store_common(b, ev, addr, value, width, false)
    }

    pub fn poison(
        &mut self,
        b: &Builder<'a>,
        ev: &mut CachingEvaluator<'a, '_, eval::Public>,
        addr: TWire<'a, u64>,
        value: TWire<'a, u64>,
        width: MemOpWidth,
    ) {
        self.store_common(b, ev, addr, value, width, true)
    }

    fn store_common(
        &mut self,
        b: &Builder<'a>,
        ev: &mut CachingEvaluator<'a, '_, eval::Public>,
        addr: TWire<'a, u64>,
        value: TWire<'a, u64>,
        width: MemOpWidth,
        poisoned: bool,
    ) {
        let public_addr = ev.eval_typed(addr);

        if let Some(public_addr) = public_addr {
            self.store_public(b, public_addr, value, width, poisoned);
        } else {
            let addr_expr = wire_arith_expr(ev, addr);
            let addr_range = arith_expr_range(addr_expr, &self.wire_range);
            let byte_range = addr_range.and_then(|(start, end)| {
                let end = end.checked_add(width.bytes() as u64 - 1)?;
                Some((start, end))
            });
            if let Some((start, end)) = byte_range {
                self.clear_range(start, end);
            } else {
                // The write address is entirely unknown.  Afterward, we can no longer be sure
                // about the value of any address.
                self.clear();
            }
        }
    }

    fn store_public(
        &mut self,
        b: &Builder<'a>,
        addr: u64,
        value: TWire<'a, u64>,
        width: MemOpWidth,
        poisoned: bool,
    ) {
        assert!(addr % width.bytes() as u64 == 0);
        let end = end_addr(addr, width);
        let (waddr, _offset) = split_mem_addr(addr);

        // Remove any entries that would be entirely overlapped by this one.
        let mut to_remove = ArrayVec::<[_; 8]>::new();
        for (&mem_addr, entry) in self.mem.range(addr ..= end) {
            if mem_addr == addr {
                if entry.width < width {
                    to_remove.push(mem_addr);
                }
            } else {
                to_remove.push(mem_addr);
            }
        }
        for remove_addr in to_remove {
            self.mem.remove(&remove_addr);
        }

        // Check if some existing entry entirely overlaps the new one.
        debug_assert!(end - waddr + 1 <= WORD_BYTES as u64);
        for (&mem_addr, entry) in self.mem.range_mut(waddr ..= end) {
            let mem_end = end_addr(mem_addr, entry.width);
            if mem_end < addr {
                continue;
            }
            // Otherwise, this `mem` entry overlaps `addr ..= end`.

            entry.value = replace_byte_range(
                b,
                entry.width.bytes() as u64, entry.value,
                addr - mem_addr, end - mem_addr + 1, value,
            );
            entry.poisoned |= poisoned;
            return;
        }

        // No entry overlaps this one.
        let value = if width < MemOpWidth::WORD {
            // Make sure the value doesn't have any extra high bits set.
            extract_byte_range_extended(b, value, 0, width.bytes() as u64)
        } else {
            value
        };
        self.mem.insert(addr, MemEntry { width, value, poisoned });
    }

    pub fn clear(&mut self) {
        self.mem.clear();
        self.default = None;
        self.default_erased = RangeSet::new();
    }

    pub fn clear_range(&mut self, start: u64, end: u64) {
        let mut remove_keys = Vec::new();
        let mut check_range = |start, end| {
            for (&mem_addr, entry) in self.mem.range(start ..= end) {
                let mem_end = end_addr(mem_addr, entry.width);
                if mem_end >= start {
                    // `mem_addr .. mem_end` overlaps `start .. end`.  We could reduce `entry` to
                    // only the nonoverlapping portion, but that would be tricky, since `start` and
                    // `end` are not required to be aligned.
                    remove_keys.push(mem_addr);
                }
            }
        };
        if start <= end {
            check_range(start, end);
        } else {
            check_range(start, u64::MAX);
            check_range(0, end);
        }

        for mem_addr in remove_keys {
            self.mem.remove(&mem_addr);
        }

        if self.default.is_some() {
            self.default_erased.insert(start, end);
        }
    }
}

/// Get the address of the final byte (inclusive) modified by an access at `addr` of the given
/// `width`.
fn end_addr(addr: u64, width: MemOpWidth) -> u64 {
    addr + (width.bytes() as u64 - 1)
}

fn split_mem_addr(addr: u64) -> (u64, ByteOffset) {
    let offset_mask = (1_u64 << WORD_LOG_BYTES) - 1;
    debug_assert!(offset_mask <= u8::MAX as u64);
    let word_addr = addr & !offset_mask;
    let offset = ByteOffset::new((addr & offset_mask) as u8);
    (word_addr, offset)
}

/// Extract bytes `lo .. hi` from `value`.  Returns a `Wire` with a width of `(hi - lo) * 8` bits.
///
/// Note that this function uses exclusive ranges (`lo .. hi`) rather than inclusive ones.
fn extract_byte_range<'a>(
    b: &Builder<'a>,
    value: TWire<'a, u64>,
    lo: u64,
    hi: u64,
) -> Wire<'a> {
    debug_assert!(lo <= hi);
    debug_assert!(hi <= WORD_BYTES as u64);
    bit_pack::extract_bits(
        b.circuit(),
        value.repr,
        (lo * 8) as u16,
        (hi * 8) as u16,
    )
}

/// Extract bytes `lo .. hi` from `value`, then return the result zero-extended to 64 bits.
///
/// Note that this function uses exclusive ranges (`lo .. hi`) rather than inclusive ones.
fn extract_byte_range_extended<'a>(
    b: &Builder<'a>,
    value: TWire<'a, u64>,
    lo: u64,
    hi: u64,
) -> TWire<'a, u64> {
    let w = extract_byte_range(b, value, lo, hi);
    let w = b.circuit().cast(w, b.circuit().ty(TyKind::U64));
    TWire::new(w)
}

/// Replace the subset of bytes at the range `new_lo .. new_hi` within `orig` with `new_value`.
/// `orig_size` is the width in bytes of the meaningful part of the value `orig`.
///
/// Note that this function uses exclusive ranges (`new_lo .. new_hi`) rather than inclusive ones.
fn replace_byte_range<'a>(
    b: &Builder<'a>,
    orig_size: u64,
    orig: TWire<'a, u64>,
    new_lo: u64,
    new_hi: u64,
    new_value: TWire<'a, u64>,
) -> TWire<'a, u64> {
    debug_assert!(new_lo <= new_hi);
    debug_assert!(new_hi <= orig_size);
    debug_assert!(orig_size <= WORD_BYTES as u64);
    let mut parts = ArrayVec::<[_; 3]>::new();
    if 0 < new_lo {
        parts.push(extract_byte_range(b, orig, 0, new_lo));
    }
    if new_lo < new_hi {
        parts.push(extract_byte_range(b, new_value, 0, new_hi - new_lo));
    }
    if new_hi < orig_size {
        parts.push(extract_byte_range(b, orig, new_hi, orig_size));
    }
    let w = bit_pack::concat_bits_raw(b.circuit(), &parts);
    let w = b.circuit().cast(w, b.circuit().ty(TyKind::U64));
    TWire::new(w)
}


/// Represents the expression `base * scale + offset`.
#[derive(Clone, Copy, Debug)]
struct ArithExpr<'a> {
    base: Option<TWire<'a, u64>>,
    scale: Wrapping<u64>,
    offset: Wrapping<u64>,
}

impl<'a> ArithExpr<'a> {
    pub fn new(base: Option<TWire<'a, u64>>, scale: u64, offset: u64) -> ArithExpr<'a> {
        ArithExpr::make(base, Wrapping(scale), Wrapping(offset))
    }

    pub fn new_wire(base: TWire<'a, u64>) -> ArithExpr<'a> {
        ArithExpr::new(Some(base), 1, 0)
    }

    pub fn new_constant(value: u64) -> ArithExpr<'a> {
        ArithExpr::new(None, 0, value)
    }

    fn make(
        base: Option<TWire<'a, u64>>,
        scale: Wrapping<u64>,
        offset: Wrapping<u64>,
    ) -> ArithExpr<'a> {
        let (base, scale) = if base.is_none() || scale == Wrapping(0) {
            (None, Wrapping(0))
        } else {
            (base, scale)
        };
        ArithExpr { base, scale, offset }
    }

    pub fn neg(self) -> ArithExpr<'a> {
        ArithExpr::make(self.base, -self.scale, -self.offset)
    }

    pub fn add(self, other: ArithExpr<'a>) -> Option<ArithExpr<'a>> {
        let (base, scale) = match (self.base, other.base) {
            (None, None) => (None, Wrapping(0)),
            (Some(x), None) => (Some(x), self.scale),
            (None, Some(y)) => (Some(y), other.scale),
            (Some(x), Some(y)) => {
                if x != y {
                    // Can't express a combination of two secret wires as a single ArithExpr.
                    return None;
                }
                (Some(x), self.scale + other.scale)
            },
        };
        Some(ArithExpr::make(base, scale, self.offset + other.offset))
    }

    pub fn sub(self, other: ArithExpr<'a>) -> Option<ArithExpr<'a>> {
        let (base, scale) = match (self.base, other.base) {
            (None, None) => (None, Wrapping(0)),
            (Some(x), None) => (Some(x), self.scale),
            (None, Some(y)) => (Some(y), other.scale),
            (Some(x), Some(y)) => {
                if x != y {
                    // Can't express a combination of two secret wires as a single ArithExpr.
                    return None;
                }
                (Some(x), self.scale - other.scale)
            },
        };
        Some(ArithExpr::make(base, scale, self.offset - other.offset))
    }

    pub fn mul(self, other: ArithExpr<'a>) -> Option<ArithExpr<'a>> {
        let (base, scale) = match (self.base, other.base) {
            (None, None) => (None, Wrapping(0)),
            (Some(x), None) => (Some(x), self.scale * other.offset),
            (None, Some(y)) => (Some(y), other.scale * self.offset),
            (Some(_), Some(_)) => return None,
        };
        Some(ArithExpr::make(base, scale, self.offset * other.offset))
    }
}

fn wire_arith_expr<'a>(
    ev: &mut CachingEvaluator<'a, '_, eval::Public>,
    w: TWire<'a, u64>,
) -> ArithExpr<'a> {
    if let Some(value) = ev.eval_typed(w) {
        return ArithExpr::new_constant(value);
    }

    let result = match w.repr.kind {
        GateKind::Unary(UnOp::Neg, a) =>
            Some(wire_arith_expr(ev, TWire::new(a)).neg()),
        GateKind::Binary(BinOp::Add, a, b) => {
            wire_arith_expr(ev, TWire::new(a))
                .add(wire_arith_expr(ev, TWire::new(b)))
        },
        GateKind::Binary(BinOp::Sub, a, b) => {
            wire_arith_expr(ev, TWire::new(a))
                .sub(wire_arith_expr(ev, TWire::new(b)))
        },
        GateKind::Binary(BinOp::Mul, a, b) => {
            wire_arith_expr(ev, TWire::new(a))
                .mul(wire_arith_expr(ev, TWire::new(b)))
        },
        _ => None,
    };
    result.unwrap_or_else(|| ArithExpr::new_wire(w))
}

/// Try to compute the range of values that `expr` might have.  Returns `Some((start, end))` to
/// indicate that the value is publicly known to be in the range `start ..= end`, or `None` if the
/// value can't be constrained to any range (aside from `0 ..= u64::MAX`).  If `end < start`, then
/// the range wraps around: `expr` could have any value in the range `start ..= u64::MAX` or any
/// value in the range `0 ..= end`.
fn arith_expr_range<'a>(
    expr: ArithExpr<'a>,
    wire_range: &HashMap<TWire<'a, u64>, u64>,
) -> Option<(u64, u64)> {
    let base = match expr.base {
        Some(x) => x,
        None => return Some((expr.offset.0, expr.offset.0)),
    };

    let max = wire_range.get(&base).cloned()?;

    let (start, end) = if let Some(scaled_max) = max.checked_mul(expr.scale.0) {
        (0, scaled_max)
    } else if let Some(neg_scaled_max) = max.checked_mul((-expr.scale).0) {
        // This case handles negative `scale` values.  These need separate handling since the
        // previous case will always overflow on a `scale` value like -1 (since it uses unsigned
        // arithmetic).  But if `-scale` is small enough, we can still compute an in-bounds range
        // covering `max * scale ..= 0`.
        (neg_scaled_max.wrapping_neg(), 0)
    } else {
        // If the arithmetic overflows, then the covered range wraps around the entire 64-bit
        // space.  We return `None` to indicate we can't determine any particular bounds on the
        // value.
        return None;
    };

    let start = start.wrapping_add(expr.offset.0);
    let end = end.wrapping_add(expr.offset.0);
    Some((start, end))
}


#[derive(Clone, Default, Debug)]
struct RangeSet {
    /// The ranges in the set.  For each inclusive range `start ..= end`, this map contains an
    /// entry with `end` as the key and `start` as the value.
    ranges: BTreeMap<u64, u64>,
}

impl RangeSet {
    pub fn new() -> RangeSet {
        RangeSet::default()
    }

    pub fn insert(&mut self, start: u64, end: u64) {
        let (mut start, mut end) = (start, end);
        loop {
            if let Some((&entry_end, entry_start)) = self.ranges.range_mut(start..).next() {
                if *entry_start <= end {
                    start = cmp::min(*entry_start, start);
                    end = cmp::max(entry_end, end);
                    self.ranges.remove(&entry_end);
                    // Try again, this time inserting the union of the two ranges.
                    continue;
                }
            }
            // There is no overlapping entry, so insert `start ..= end` on its own.
            self.ranges.insert(end, start);
            break;
        }
    }

    pub fn overlaps(&self, start: u64, end: u64) -> bool {
        if let Some((&_erase_end, &erase_start)) = self.ranges.range(start..).next() {
            // We're checking for overlap between the inclusive ranges `start ..= end` and
            // `erase_start ..= erase_end`.  Normally, this check would consist of `erase_start <=
            // end && erase_end >= start`.  But we already know that `erase_end >= start` due to
            // the argument to `BTreeMap::range`, so we only need to explicitly check that
            // `erase_start <= end`.
            if erase_start <= end {
                return true;
            }
        }
        false
    }
}


#[cfg(test)]
mod test {
    use bumpalo::Bump;
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::{Circuit, DynCircuit};
    use crate::ir::typed::{Builder, EvaluatorExt};
    use super::*;

    #[test]
    fn bytes() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0));
        for i in 0..8 {
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1, false);
        }

        for i in 0..8 {
            let w = m.load_public(&b, i, MemOpWidth::W1).unwrap();
            let v = ev.eval_typed(w).unwrap();
            assert_eq!(v, i + 1);
        }
    }

    #[test]
    fn bytes_to_word() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0));
        for i in 0..8 {
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1, false);
        }

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }

    #[test]
    fn word_to_bytes() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0));
        m.store_public(&b, 0, b.lit(0x0807060504030201), MemOpWidth::W8, false);

        for i in 0..8 {
            let w = m.load_public(&b, i, MemOpWidth::W1).unwrap();
            let v = ev.eval_typed(w).unwrap();
            assert_eq!(v, i + 1);
        }
    }

    /// Store bytes, then load as a word, with gaps between the bytes.  This exercises the cases of
    /// `load_public` that add padding using the `default` value.
    #[test]
    fn bytes_to_word_with_gaps() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0x8877665544332211));
        for &i in &[1,2,3,5,6] {
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1, false);
        }

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x8807065504030211);
    }

    /// Store bytes, then load as a word, with no `default` value.  This should succeed, since
    /// every byte is written with a known value.
    #[test]
    fn bytes_to_word_no_default() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::new();
        for i in 0..8 {
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1, false);
        }

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }

    /// Store bytes, then load as a word, with gaps between the bytes, and with no `default` value.
    /// This should fail, since there's no default to fill in the gaps.
    #[test]
    fn bytes_to_word_with_gaps_no_default() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));

        let mut m = KnownMem::new();
        for &i in &[1,2,3,5,6] {
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1, false);
        }

        assert!(m.load_public(&b, 0, MemOpWidth::W8).is_none());
    }

    /// Overwrite some smaller entries with a single large one.
    #[test]
    fn overwrite_smaller() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0));
        for &i in &[1,2,3,5,6] {
            m.store_public(&b, i, b.lit(i + 3), MemOpWidth::W1, false);
        }
        m.store_public(&b, 0, b.lit(0x0201), MemOpWidth::W2, false);
        m.store_public(&b, 2, b.lit(0x0403), MemOpWidth::W2, false);
        m.store_public(&b, 4, b.lit(0x08070605), MemOpWidth::W4, false);
        // All the one-byte writes should have been removed.
        assert!(m.mem.len() == 3);

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }

    /// Overwrite parts of a large write with smaller ones.
    #[test]
    fn overwrite_larger() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0));
        m.store_public(&b, 0, b.lit(0x0000000000000201), MemOpWidth::W8, false);
        m.store_public(&b, 2, b.lit(0x0403), MemOpWidth::W2, false);
        m.store_public(&b, 4, b.lit(0x08070605), MemOpWidth::W4, false);
        assert!(m.mem.len() == 1);

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }

    /// Overwrite one entry with one of the same size.
    #[test]
    fn overwrite_same_size() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let mut m = KnownMem::with_default(b.lit(0));
        m.store_public(&b, 0, b.lit(0), MemOpWidth::W2, false);
        m.store_public(&b, 2, b.lit(0), MemOpWidth::W2, false);
        m.store_public(&b, 4, b.lit(0), MemOpWidth::W4, false);
        m.store_public(&b, 0, b.lit(0x0201), MemOpWidth::W2, false);
        m.store_public(&b, 2, b.lit(0x0403), MemOpWidth::W2, false);
        m.store_public(&b, 4, b.lit(0x08070605), MemOpWidth::W4, false);

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }


    /// Check behavior of loads near the end of the address space.
    #[test]
    fn load_end() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let waddr = u64::MAX - 7;
        let mut m = KnownMem::with_default(b.lit(0));
        // We store to all of the last word except its final byte, since touching the last byte
        // could cause problems on the `store`.
        m.store_public(&b, waddr + 0, b.lit(0x04030201), MemOpWidth::W4, false);
        m.store_public(&b, waddr + 4, b.lit(0x0605), MemOpWidth::W2, false);
        m.store_public(&b, waddr + 6, b.lit(0x07), MemOpWidth::W1, false);

        // These three exercise the cases where `entry.width < width`.
        let w = m.load_public(&b, waddr + 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0007060504030201);

        let w = m.load_public(&b, waddr + 4, MemOpWidth::W4).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x00070605);

        let w = m.load_public(&b, waddr + 6, MemOpWidth::W2).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0007);

        // This one exercises the case where there are no overlapping entries.
        let w = m.load_public(&b, waddr + 7, MemOpWidth::W1).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x00);
    }

    /// Check behavior of loads near the end of the address space.
    #[test]
    fn load_end_word() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let waddr = u64::MAX - 7;
        let mut m = KnownMem::with_default(b.lit(0));
        m.store_public(&b, waddr + 0, b.lit(0x0807060504030201), MemOpWidth::W8, false);

        // These four exercise the case where `entry.width >= width`.
        let w = m.load_public(&b, waddr + 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);

        let w = m.load_public(&b, waddr + 4, MemOpWidth::W4).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x08070605);

        let w = m.load_public(&b, waddr + 6, MemOpWidth::W2).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807);

        let w = m.load_public(&b, waddr + 7, MemOpWidth::W1).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x08);
    }

    /// Check behavior of stores near the end of the address space.
    #[test]
    fn store_end_overwrite() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let waddr = u64::MAX - 7;
        let mut m = KnownMem::with_default(b.lit(0));
        // These four exercise the case of overwriting parts of a larger entry.
        m.store_public(&b, waddr + 0, b.lit(0x0807060504030201), MemOpWidth::W8, false);
        m.store_public(&b, waddr + 4, b.lit(0x18171615), MemOpWidth::W4, false);
        m.store_public(&b, waddr + 6, b.lit(0x2827), MemOpWidth::W2, false);
        m.store_public(&b, waddr + 7, b.lit(0x38), MemOpWidth::W1, false);

        let w = m.load_public(&b, waddr + 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x3827161504030201);
    }

    /// Check behavior of stores near the end of the address space.
    #[test]
    fn store_end_replace() {
        let arena = Bump::new();
        let c = Circuit::new(&arena, true);
        let b = Builder::new(DynCircuit::new(&c));
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);

        let waddr = u64::MAX - 7;
        let mut m = KnownMem::with_default(b.lit(0));
        // These four exercise the case of replacing smaller overlapping entries.
        m.store_public(&b, waddr + 7, b.lit(0x38), MemOpWidth::W1, false);
        m.store_public(&b, waddr + 6, b.lit(0x2827), MemOpWidth::W2, false);
        m.store_public(&b, waddr + 4, b.lit(0x18171615), MemOpWidth::W4, false);
        m.store_public(&b, waddr + 0, b.lit(0x0807060504030201), MemOpWidth::W8, false);

        let w = m.load_public(&b, waddr + 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }


    #[test]
    fn range_set_overlaps() {
        let mut rs = RangeSet::new();
        rs.insert(1, 1);
        rs.insert(3, 5);
        rs.insert(10, 20);
        assert_eq!(rs.overlaps(0, 0), false);
        assert_eq!(rs.overlaps(0, 1), true);
        assert_eq!(rs.overlaps(1, 1), true);
        assert_eq!(rs.overlaps(1, 2), true);
        assert_eq!(rs.overlaps(2, 2), false);
        assert_eq!(rs.overlaps(0, 2), true);
        assert_eq!(rs.overlaps(6, 9), false);
        assert_eq!(rs.overlaps(20, 30), true);
        assert_eq!(rs.overlaps(21, 30), false);
        assert_eq!(rs.overlaps(0, 6), true);
    }

    #[test]
    fn range_set_insert() {
        let mut rs = RangeSet::new();
        rs.insert(1, 1);
        rs.insert(1, 2);
        assert_eq!(rs.ranges.clone().into_iter().collect::<Vec<_>>(),
            vec![(2, 1)]);
        rs.insert(3, 4);
        assert_eq!(rs.ranges.clone().into_iter().collect::<Vec<_>>(),
            vec![(2, 1), (4, 3)]);
        rs.insert(2, 3);
        assert_eq!(rs.ranges.clone().into_iter().collect::<Vec<_>>(),
            vec![(4, 1)]);

        rs.insert(10, 11);
        rs.insert(13, 14);
        rs.insert(16, 17);
        assert_eq!(rs.ranges.clone().into_iter().collect::<Vec<_>>(),
            vec![(4, 1), (11, 10), (14, 13), (17, 16)]);
        rs.insert(11, 20);
        assert_eq!(rs.ranges.clone().into_iter().collect::<Vec<_>>(),
            vec![(4, 1), (20, 10)]);
    }
}
