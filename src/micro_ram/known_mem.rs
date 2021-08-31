use std::collections::BTreeMap;
use arrayvec::ArrayVec;
use crate::gadget::bit_pack;
use crate::ir::circuit::{Wire, GateKind, TyKind, CircuitTrait, CircuitExt};
use crate::ir::typed::{TWire, Builder};
use crate::micro_ram::types::{MemOpWidth, WORD_BYTES, WORD_LOG_BYTES, ByteOffset};

/// The known contents of memory at some point in the execution.  This is used to resolve some
/// memory loads to a wire containing the value without using an actual memory port.
#[derive(Clone, Debug, Default)]
pub struct KnownMem<'a> {
    mem: BTreeMap<u64, (MemOpWidth, TWire<'a, u64>)>,
    default: Option<TWire<'a, u64>>,
}

impl<'a> KnownMem<'a> {
    pub fn new() -> KnownMem<'a> {
        KnownMem::default()
    }

    pub fn with_default(default: TWire<'a, u64>) -> KnownMem<'a> {
        KnownMem {
            default: Some(default),
            .. KnownMem::default()
        }
    }

    pub fn load(
        &mut self,
        b: &Builder<'a>,
        addr: TWire<'a, u64>,
        width: MemOpWidth,
    ) -> Option<TWire<'a, u64>> {
        // Get the address being loaded as a `u64`.  If the address isn't a constant, then we can't
        // determine anything about the value.
        let public_addr = match addr.repr.kind {
            GateKind::Lit(bits, _) => bits.as_u64()?,
            _ => return None,
        };
        self.load_public(b, public_addr, width)
    }

    fn load_public(
        &mut self,
        b: &Builder<'a>,
        addr: u64,
        width: MemOpWidth,
    ) -> Option<TWire<'a, u64>> {
        assert!(addr % width.bytes() as u64 == 0);
        let end = addr + width.bytes() as u64;
        let (waddr, _offset) = split_mem_addr(addr);

        let mut parts = ArrayVec::<[_; WORD_BYTES]>::new();
        // The contents of `parts` covers the range `addr .. parts_end`.
        let mut parts_end = addr;

        debug_assert!(end - waddr <= WORD_BYTES as u64);
        for (&mem_addr, &(mem_width, mem_value)) in self.mem.range(waddr .. end) {
            let mem_end = mem_addr + mem_width.bytes() as u64;
            if mem_end <= addr {
                continue;
            }
            // Otherwise, this `mem` entry overlaps `addr .. end`.

            if mem_width >= width {
                // This entry covers the entire load.
                debug_assert!(parts.len() == 0);
                debug_assert!(mem_end >= end);
                return Some(extract_byte_range_extended(b, mem_value, mem_addr, addr, end));
            } else {
                // This entry covers a strict subset of the load.

                if parts_end < mem_addr {
                    // Add part of the default value.
                    let default = self.default?;
                    let padding = extract_byte_range(b, default, waddr, parts_end, mem_addr);
                    parts.push(padding);
                    parts_end = mem_addr;
                }

                let part = extract_byte_range(b, mem_value, mem_addr, parts_end, mem_end);
                parts.push(part);
                parts_end = mem_end;
            }
        }

        if parts_end < end {
            let default = self.default?;
            let padding = extract_byte_range(b, default, waddr, parts_end, end);
            parts.push(padding);
        }

        let w = bit_pack::concat_bits_raw(b.circuit(), &parts);
        let w = b.circuit().cast(w, b.circuit().ty(TyKind::U64));
        Some(TWire::new(w))
    }

    pub fn store(
        &mut self,
        b: &Builder<'a>,
        addr: TWire<'a, u64>,
        value: TWire<'a, u64>,
        width: MemOpWidth,
    ) {
        let public_addr = match addr.repr.kind {
            GateKind::Lit(bits, _) => bits.as_u64(),
            _ => None,
        };

        if let Some(public_addr) = public_addr {
            self.store_public(b, public_addr, value, width);
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
    ) {
        assert!(addr % width.bytes() as u64 == 0);
        let end = addr + width.bytes() as u64;
        let (waddr, _offset) = split_mem_addr(addr);

        // Remove any entries that would be entirely overlapped by this one.
        let mut to_remove = ArrayVec::<[_; 8]>::new();
        for (&mem_addr, &(mem_width, _)) in self.mem.range(addr .. end) {
            if mem_addr == addr {
                if mem_width < width {
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
        debug_assert!(end - waddr <= WORD_BYTES as u64);
        for (&mem_addr, &mut (mem_width, ref mut mem_value)) in self.mem.range_mut(waddr .. end) {
            let mem_end = mem_addr + mem_width.bytes() as u64;
            if mem_end <= addr {
                continue;
            }
            // Otherwise, this `mem` entry overlaps `addr .. end`.

            *mem_value = replace_byte_range(
                b,
                mem_addr, mem_end, *mem_value,
                addr, end, value,
            );
            return;
        }

        // No entry overlaps this one.
        let value = if width < MemOpWidth::WORD {
            // Make sure the value doesn't have any extra high bits set.
            extract_byte_range_extended(b, value, 0, 0, width.bytes() as u64)
        } else {
            value
        };
        self.mem.insert(addr, (width, value));
    }

    pub fn clear(&mut self) {
        self.mem.clear();
        self.default = None;
    }
}

fn split_mem_addr(addr: u64) -> (u64, ByteOffset) {
    let offset_mask = (1_u64 << WORD_LOG_BYTES) - 1;
    debug_assert!(offset_mask <= u8::MAX as u64);
    let word_addr = addr & !offset_mask;
    let offset = ByteOffset::new((addr & offset_mask) as u8);
    (word_addr, offset)
}

fn extract_byte_range<'a>(
    b: &Builder<'a>,
    value: TWire<'a, u64>,
    value_start: u64,
    lo: u64,
    hi: u64,
) -> Wire<'a> {
    debug_assert!(value_start <= lo);
    debug_assert!(lo <= hi);
    debug_assert!(hi - value_start <= WORD_BYTES as u64);
    bit_pack::extract_bits(
        b.circuit(),
        value.repr,
        ((lo - value_start) * 8) as u16,
        ((hi - value_start) * 8) as u16,
    )
}

fn extract_byte_range_extended<'a>(
    b: &Builder<'a>,
    value: TWire<'a, u64>,
    value_start: u64,
    lo: u64,
    hi: u64,
) -> TWire<'a, u64> {
    let w = extract_byte_range(b, value, value_start, lo, hi);
    let w = b.circuit().cast(w, b.circuit().ty(TyKind::U64));
    TWire::new(w)
}

fn replace_byte_range<'a>(
    b: &Builder<'a>,
    orig_start: u64,
    orig_end: u64,
    orig: TWire<'a, u64>,
    new_start: u64,
    new_end: u64,
    new_value: TWire<'a, u64>,
) -> TWire<'a, u64> {
    debug_assert!(orig_start <= new_start);
    debug_assert!(new_start <= new_end);
    debug_assert!(new_end <= orig_end);
    debug_assert!(orig_end - orig_start <= WORD_BYTES as u64);
    let mut parts = ArrayVec::<[_; 3]>::new();
    if orig_start < new_start {
        parts.push(extract_byte_range(b, orig, orig_start, orig_start, new_start));
    }
    if new_start < new_end {
        parts.push(extract_byte_range(b, new_value, new_start, new_start, new_end));
    }
    if new_end < orig_end {
        parts.push(extract_byte_range(b, orig, orig_start, new_end, orig_end));
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
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1);
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
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1);
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
        m.store_public(&b, 0, b.lit(0x0807060504030201), MemOpWidth::W8);

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
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1);
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
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1);
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
            m.store_public(&b, i, b.lit(i + 1), MemOpWidth::W1);
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
            m.store_public(&b, i, b.lit(i + 3), MemOpWidth::W1);
        }
        m.store_public(&b, 0, b.lit(0x0201), MemOpWidth::W2);
        m.store_public(&b, 2, b.lit(0x0403), MemOpWidth::W2);
        m.store_public(&b, 4, b.lit(0x08070605), MemOpWidth::W4);
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
        m.store_public(&b, 0, b.lit(0x0000000000000201), MemOpWidth::W8);
        m.store_public(&b, 2, b.lit(0x0403), MemOpWidth::W2);
        m.store_public(&b, 4, b.lit(0x08070605), MemOpWidth::W4);
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
        m.store_public(&b, 0, b.lit(0), MemOpWidth::W2);
        m.store_public(&b, 2, b.lit(0), MemOpWidth::W2);
        m.store_public(&b, 4, b.lit(0), MemOpWidth::W4);
        m.store_public(&b, 0, b.lit(0x0201), MemOpWidth::W2);
        m.store_public(&b, 2, b.lit(0x0403), MemOpWidth::W2);
        m.store_public(&b, 4, b.lit(0x08070605), MemOpWidth::W4);

        let w = m.load_public(&b, 0, MemOpWidth::W8).unwrap();
        let v = ev.eval_typed(w).unwrap();
        assert_eq!(v, 0x0807060504030201);
    }
}
