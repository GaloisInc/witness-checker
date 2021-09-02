use std::collections::BTreeMap;
use arrayvec::ArrayVec;
use crate::eval::{self, CachingEvaluator};
use crate::gadget::bit_pack;
use crate::ir::circuit::{Wire, TyKind, CircuitTrait, CircuitExt};
use crate::ir::typed::{TWire, Builder, EvaluatorExt};
use crate::micro_ram::types::{MemOpWidth, WORD_BYTES, WORD_LOG_BYTES, ByteOffset, MemSegment};

/// The known contents of memory at some point in the execution.  This is used to resolve some
/// memory loads to a wire containing the value without using an actual memory port.
#[derive(Clone, Debug, Default)]
pub struct KnownMem<'a> {
    mem: BTreeMap<u64, MemEntry<'a>>,
    default: Option<TWire<'a, u64>>,
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
            let lo = addr + parts_bytes - waddr;
            let hi = end - waddr + 1;
            let padding = extract_byte_range(b, default, lo, hi);
            parts.push(padding);
        }

        let w = bit_pack::concat_bits_raw(b.circuit(), &parts);
        let w = b.circuit().cast(w, b.circuit().ty(TyKind::U64));
        Some(TWire::new(w))
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
            // The write modifies an unknown address.  Afterward, we can no longer be sure about
            // the value of any address.
            self.clear();
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
}
