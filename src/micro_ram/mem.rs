//! Memory consistency check.
//!
//! This includes setting up initial memory, adding `MemPort`s for each cycle, sorting, and
//! checking the sorted list.
use std::convert::TryFrom;
use std::iter;
use log::*;
use crate::gadget::bit_pack;
use crate::ir::typed::{TWire, TSecretHandle, Builder, Flatten};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{
    MemPort, MemOpKind, MemOpWidth, PackedMemPort, Label, PackedLabel, MemSegment, ByteOffset, WordAddr,
    MEM_PORT_PRELOAD_CYCLE, MEM_PORT_UNUSED_CYCLE, WORD_BYTES,
};
use crate::mode::if_mode::{AnyTainted, IfMode, is_mode};
use crate::mode::tainted::{self, PACKED_UNTAINTED};
use crate::sort;

pub struct Memory<'a> {
    ports: Vec<TWire<'a, MemPort>>,
}

impl<'a> Memory<'a> {
    pub fn new() -> Memory<'a> {
        Memory {
            ports: Vec::new(),
        }
    }

    pub fn init_segment(&mut self, b: &Builder<'a>, seg: &MemSegment) {
        self.ports.reserve(seg.len as usize);

        for i in 0 .. seg.len {
            // Initial memory values are given in terms of words, not bytes.
            let waddr = seg.start + i;


            // Most of the MemPort is public.  Only the value and taint are secret, if `seg.secret` is set.
            let mut mp = b.lit(MemPort {
                cycle: MEM_PORT_PRELOAD_CYCLE,
                addr: waddr * MemOpWidth::WORD.bytes() as u64,
                // Dummy value for now.  We fill in this field differently depending on `prover`
                // and `seg.secret`.
                value: 0,
                op: MemOpKind::Write,
                tainted: IfMode::new(|pf| PACKED_UNTAINTED),
                width: MemOpWidth::WORD,
            });

            // Get the value of the word at index `i`.  `data` is implicitly zero-padded out to
            // `seg.len`, to support `.bss`-style zero-initialized segments.  For secret segments
            // in verifier mode, `seg.data` is always empty, so the `value` is zero (but unused).
            let value = seg.data.get(i as usize).cloned().unwrap_or(0);
            if seg.secret {
                mp.value = b.secret_init(|| value);
            } else {
                mp.value = b.lit(value);
            }

            mp.tainted = {
                let t: IfMode<_, PackedLabel> = IfMode::new(|pf| {
                    seg.tainted.as_ref().unwrap(&pf).get(i as usize).cloned().unwrap_or(0)
                });
                if seg.secret {
                    b.secret_init(|| t)
                } else {
                    b.lit(t)
                }
            };

            self.ports.push(mp);
        }
    }

    pub fn add_cycles<'b>(
        &mut self,
        cx: &Context<'a>,
        b: &Builder<'a>,
        len: usize,
        sparsity: usize,
    ) -> CyclePorts<'a> {
        self.add_cycles_irregular(cx, b, len, (0 .. len).step_by(sparsity))
    }

    pub fn add_cycles_irregular<'b>(
        &mut self,
        cx: &Context<'a>,
        b: &Builder<'a>,
        len: usize,
        idxs: impl IntoIterator<Item = usize>,
    ) -> CyclePorts<'a> {
        let mut cp = CyclePorts {
            port_starts: idxs.into_iter().chain(iter::once(len))
                .map(|i| u32::try_from(i).unwrap()).collect(),
            ports: Vec::new(),
        };
        assert!((1 .. cp.port_starts.len()).all(|i| cp.port_starts[i - 1] < cp.port_starts[i]));

        let num_ports = cp.port_starts.len() - 1;
        cp.ports.reserve(num_ports);
        for i in 0 .. num_ports {
// <<<<<<< HEAD
//             // Find the `MemOp` advice in this block (if any) and build the mem port.
//             let mut mp = None;
//             let mut found_j = None;
//             for j in i * sparsity .. (i + 1) * sparsity {
//                 let (advs, cycle) = get_advice(j);
//                 for adv in advs {
//                     if let Advice::MemOp { addr, value, op, tainted } = *adv {
//                         if let Some(found_j) = found_j {
//                             panic!(
//                                 "multiple mem ports in block {}: cycle {}, cycle {}",
//                                 i, found_j, j,
//                             );
//                         }
//                         found_j = Some(j);
//                         mp = Some(MemPort { cycle, addr, value, op, tainted });
//                     }
//                 }
//             }
// 
//             let mp = mp.unwrap_or_else(|| MemPort {
// =======
            let (mp, mp_secret) = b.secret_default(MemPort {
// >>>>>>> master
                cycle: MEM_PORT_UNUSED_CYCLE,
                // We want all in-use `MemPort`s to be distinct, since it simplifies checking the
                // correspondence between `MemPort`s and steps.  We make unused ports distinct too,
                // so we can just check that all ports are distinct.
                addr: (self.ports.len() + i) as u64 * MemOpWidth::WORD.bytes() as u64,
                value: 0,
                op: MemOpKind::Write,
                tainted: IfMode::new(|fp| 0),
                width: MemOpWidth::WORD,
            });
            let (user, user_secret) = b.secret_default(0);
            cp.ports.push(SparseMemPort {
                mp, mp_secret,
                user, user_secret,
                is_set: false,
            });
        }

        cp.assert_valid(cx, b);
        self.ports.extend(cp.ports.iter().map(|smp| smp.mp));
        cp
    }

    /// Assert that this set of memory operations is internally consistent.
    ///
    /// This takes `self` by value to prevent adding more `MemPort`s after the consistency check.
    pub fn assert_consistent(self, cx: &Context<'a>, b: &Builder<'a>) {
        // Sort the memory ports by addres and then by cycle.  Most of the ordering logic is
        // handled by the `typed::Lt` impl for `PackedMemPort`.
        let sorted_ports = {
            let _g = b.scoped_label("sort mem");
            let mut packed_ports = self.ports.iter().map(|&mp| {
                PackedMemPort::from_unpacked(&b, mp)
            }).collect::<Vec<_>>();
            // Using `lt` instead of `le` for the comparison here means the sortedness check will
            // also ensure that every `MemPort` is distinct.
            let sorted = sort::sort(&b, &mut packed_ports, &mut |&x, &y| b.lt(x, y));
            wire_assert!(&cx, sorted, "memory op sorting failed");
            packed_ports.iter().map(|pmp| pmp.unpack(&b)).collect::<Vec<_>>()
        };

        // Debug logging, showing the state before and after sorting.
        trace!("mem ops:");
        for (i, port) in self.ports.iter().enumerate() {
            trace!(
                "mem op {:3}: op{}, {:x}, value {}, cycle {}",
                i, cx.eval(port.op.repr), cx.eval(port.addr), cx.eval(port.value),
                cx.eval(port.cycle),
            );
        }
        trace!("sorted mem ops:");
        for (i, port) in sorted_ports.iter().enumerate() {
            trace!(
                "mem op {:3}: op{}, {:x}, value {}, cycle {}",
                i, cx.eval(port.op.repr), cx.eval(port.addr), cx.eval(port.value),
                cx.eval(port.cycle),
            );
        }

        // Run the consistency check.
        // The first port has no previous port.  Supply a dummy port and set `prev_valid = false`.
        if sorted_ports.len() > 0 {
            check_mem(&cx, &b, 0, &sorted_ports[0], b.lit(false), sorted_ports[0]);
        }

        let it = sorted_ports.iter().zip(sorted_ports.iter().skip(1)).enumerate();
        for (i, (prev, &port)) in it {
            let prev_valid = b.eq(word_addr(b, prev.addr), word_addr(b, port.addr));
            check_mem(&cx, &b, i + 1, prev, prev_valid, port);
        }
    }
}

/// A `MemPort` that is potentially shared by several steps.
#[derive(Clone)]
pub struct SparseMemPort<'a> {
    mp: TWire<'a, MemPort>,
    /// Which of the steps actually uses this `MemPort`.  If no step uses it, the value will be out
    /// of range (`>= sparsity`).
    user: TWire<'a, u8>,
    mp_secret: TSecretHandle<'a, MemPort>,
    user_secret: TSecretHandle<'a, u8>,
    is_set: bool,
}

pub struct CyclePorts<'a> {
    /// The initial cycle covered by each port in `ports`.  `ports[i]` handles cycles in the range
    /// `port_starts[i] .. port_starts[i+1]`.  We keep an extra trailing element in `port_starts`
    /// to indicate the length (number of cycles covered) of the last port.
    port_starts: Vec<u32>,
    ports: Vec<SparseMemPort<'a>>,
}

impl<'a> CyclePorts<'a> {
    fn index_to_port(&self, i: u32) -> Option<(usize, u8)> {
        // Find the greatest element with `start <= i`.
        let idx = match self.port_starts.binary_search(&i) {
            // `Ok` means we found an entry whose start is exactly equal to `i`.
            Ok(x) => x,
            // `Err` gives the position where `i` could be inserted to keep the list sorted.  So
            // the element at the previous index is the one we want.
            Err(0) => return None,
            Err(x) => x - 1,
        };
        let user = u8::try_from(i - self.port_starts[idx]).ok()?;
        Some((idx, user))
    }

    fn port_len(&self, idx: usize) -> u8 {
        let len = self.port_starts[idx + 1] - self.port_starts[idx];
        u8::try_from(len)
            .unwrap_or_else(|_| panic!("port index {} out of range for CyclePorts", idx))
    }

    /// Get the `MemPort` used by step `i`.  Returns `MemPort::default()` if step `i` does not have
    /// a `MemPort` assigned to it.
    pub fn get(&self, b: &Builder<'a>, i: usize) -> TWire<'a, MemPort> {
        let (idx, user) = match self.index_to_port(u32::try_from(i).unwrap()) {
            Some(x) => x,
            // `None` means no port covers step `i`.
            None => return b.lit(MemPort {
                cycle: MEM_PORT_UNUSED_CYCLE,
                tainted: IfMode::new(|pf| PACKED_UNTAINTED),
                .. MemPort::default()
            }),
        };

        if self.port_len(idx) == 1 {
            // Avoid an extra mux when sparsity is disabled.
            return self.ports[idx].mp;
        }

        let smp = &self.ports[idx];
        b.mux(
            b.eq(smp.user, b.lit(user as u8)),
            smp.mp,
            b.lit(MemPort {
                cycle: MEM_PORT_UNUSED_CYCLE,
                tainted: IfMode::new(|pf| PACKED_UNTAINTED),
                .. MemPort::default()
            }),
        )
    }

    /// Initialize the `MemPort` for `i` with the values in `port`.  `i` is the index of a cycle,
    /// not a port, so it can range up to `self.ports.len() * self.sparsity` (the number of cycles
    /// covered by this `CyclePorts`), not just `self.ports.len()` (the number of actual ports).
    pub fn set_port(&mut self, b: &Builder<'a>, i: usize, port: MemPort) {
        let (idx, user) = self.index_to_port(u32::try_from(i).unwrap())
            .unwrap_or_else(|| panic!("no memory port is available for index {}", i));
        let smp = &mut self.ports[idx];
        assert!(!smp.is_set, "multiple mem ops require sparse mem port {}", idx);
        smp.mp_secret.set(b, port);
        smp.user_secret.set(b, user);
        smp.is_set = true;
    }

    pub fn iter<'b>(&'b self) -> impl Iterator<Item = SparseMemPort<'a>> + 'b {
        self.ports.iter().cloned()
    }

    /// Perform validity checks, as described in `docs/memory_sparsity.md`.
    fn assert_valid(&self, cx: &Context<'a>, b: &Builder<'a>) {
        for (i, smp) in self.ports.iter().enumerate() {
            let block_size = self.port_len(i);
            let user = smp.user;
            let ok = if block_size == 1 {
                b.eq(user, b.lit(0))
            } else {
                b.lt(user, b.lit(block_size))
            };
            wire_assert!(
                cx, ok,
                "block {} user index {} is out of range (expected < {})",
                i, cx.eval(user), block_size,
            );
        }
    }
}


/// Get the "misalignment" of an address, equal to `addr % width.bytes()`.  The result is zero for
/// well-aligned addresses.
fn addr_misalignment<'a>(
    _cx: &Context<'a>,
    b: &Builder<'a>,
// <<<<<<< HEAD
//     port: &TWire<'a, MemPort>,
// ) {
//     let _g = b.scoped_label("check_first_mem");
//     // If the first memory port is active, then it must not be a read, since there are no previous
//     // writes to read from.
//     let active = b.ne(port.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));
//     // Skip this check if we're running in tainted mode.
//     if !is_mode::<AnyTainted>() {
//         wire_bug_if!(
//             cx, b.mux(active, b.eq(port.op, b.lit(MemOpKind::Read)), b.lit(false)),
//             "uninit read from {:x} on cycle {}",
//             cx.eval(port.addr), cx.eval(port.cycle),
//         );
//     }
// =======
    addr: TWire<'a, u64>,
    width: TWire<'a, MemOpWidth>,
) -> TWire<'a, ByteOffset> {
    let mut offset = b.lit(ByteOffset::new(0));
    for lit_width in MemOpWidth::iter() {
        let cond = b.eq(width, b.lit(lit_width));
        let new_offset = TWire::<ByteOffset>::new(b.circuit().cast(
            bit_pack::extract_bits(b.circuit(), addr.repr, 0, lit_width.log_bytes() as u16),
            ByteOffset::wire_type(b.circuit()),
        ));
        offset = b.mux(cond, new_offset, offset);
    }
    offset
}

fn check_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    index: usize,
    prev: &TWire<'a, MemPort>,
    prev_valid: TWire<'a, bool>,
    port: TWire<'a, MemPort>,
) {
    let _g = b.scoped_label(format_args!("check_mem/index {}", index));
    let active = b.ne(port.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));

    // Alignment: `addr` must be a multiple of `width.bytes()`.
    let misalign = addr_misalignment(cx, b, port.addr, port.width);
    wire_assert!(
        cx, b.eq(misalign, b.lit(ByteOffset::new(0))),
        "unaligned access of {:x} with width {:?} on cycle {}",
        cx.eval(port.addr), cx.eval(port.width), cx.eval(port.cycle),
    );

    let is_read = b.eq(port.op, b.lit(MemOpKind::Read));
    let is_write = b.eq(port.op, b.lit(MemOpKind::Write));
    let is_poison = b.eq(port.op, b.lit(MemOpKind::Poison));

    cx.when(b, prev_valid, |cx| {
        cx.when(b, b.eq(prev.op, b.lit(MemOpKind::Poison)), |cx| {
            // Poison -> Poison is invalid.
            wire_assert!(
                cx, b.not(is_poison),
                "double poison of address {:x} on cycle {}",
                cx.eval(port.addr), cx.eval(port.cycle),
            );

            // Poison -> Read/Write is a bug.
            wire_bug_if!(
                cx, b.not(is_poison),
                "access of poisoned address {:x} on cycle {}",
                cx.eval(port.addr), cx.eval(port.cycle),
            );
        });
    });

    // When there is no previous op for this address (`!prev_valid`), we set `prev_value =
    // port.value`, so all the `value` equality checks below will pass.  This means uninitialized
    // reads will succeed, but the prover can provide arbitrary data for any uninitialized bytes.
    let prev_value = b.mux(prev_valid, prev.value, port.value);
    let prev_taint = b.mux(prev_valid, prev.tainted, port.tainted);

    cx.when(b, b.and(is_read, active), |cx| {
        // Reads must produce the same value as the previous operation.
        wire_assert!(
            cx, b.eq(port.value, prev_value),
            "read from {:x} on cycle {} produced {} (expected {})",
            cx.eval(port.addr), cx.eval(port.cycle),
            cx.eval(port.value), cx.eval(prev_value),
        );

        tainted::check_read_memports(cx, b, &prev_taint, &port);
    });

    cx.when(b, b.or(is_write, is_poison), |cx| {
        // Writes (and poison) may only modify the bytes identified by the `addr` offset and the
        // `width`.
        let mut mostly_eq_acc = b.lit(false);
        for w in MemOpWidth::iter() {
            let mostly_eq = compare_except_bytes_at_offset(
                b,
                port.value,
                prev_value,
                port.addr,
                w,
            );
            mostly_eq_acc = b.mux(
                b.eq(port.width, b.lit(w)),
                mostly_eq,
                mostly_eq_acc,
            );
        }
        wire_assert!(
            cx, mostly_eq_acc,
            "{:?} to {:x} on cycle {} modified outside width {:?}: 0x{:x} != 0x{:x}",
            cx.eval(port.op), cx.eval(port.addr), cx.eval(port.cycle), cx.eval(port.width),
            cx.eval(port.value), cx.eval(prev_value),
        );

        tainted::check_write_memports(cx, b, &prev_taint, &port);
    });
}


/// Extract `width` bytes from `value`, starting at the offset indicated by the low bits of `addr`.
/// The result is zero-extended to 64 bits.
pub fn extract_bytes_at_offset<'a>(
    b: &Builder<'a>,
    value: TWire<'a, u64>,
    addr: TWire<'a, u64>,
    width: MemOpWidth,
) -> TWire<'a, u64> {
    // Hard to write this as a function without const generics
    macro_rules! go {
        ($T:ty, $divisor:expr) => {{
            let value_parts = bit_pack::split_bits::<[$T; WORD_BYTES / $divisor]>(b, value.repr);
            let offset = bit_pack::extract_low::<ByteOffset>(b, addr.repr);
            // The `* d` multiply means that if `offset` is `i * d`, then `result` is
            // `value_parts[i]`.  If `offset` is not a multiple of `d`, then we return an arbitrary
            // value, on the assumption that the memory consistency alignment check will fail later
            // on.
            let result = b.index(&*value_parts, offset, |b, idx| {
                b.lit(ByteOffset::new(idx as u8 * $divisor))
            });
            b.cast(result)
        }};
    }

    match width {
        MemOpWidth::W1 => go!(u8, 1),
        MemOpWidth::W2 => go!(u16, 2),
        MemOpWidth::W4 => go!(u32, 4),
        MemOpWidth::W8 => value,
    }
}

/// Extract the low `width` bytes of `value`, zero-extended to 64 bits.
pub fn extract_low_bytes<'a>(
    b: &Builder<'a>,
    value: TWire<'a, u64>,
    width: MemOpWidth,
) -> TWire<'a, u64> {
    // Hard to write this as a function without const generics
    macro_rules! go {
        ($T:ty) => {{
            let low = bit_pack::extract_low::<$T>(b, value.repr);
            b.cast(low)
        }};
    }

    match width {
        MemOpWidth::W1 => go!(u8),
        MemOpWidth::W2 => go!(u16),
        MemOpWidth::W4 => go!(u32),
        MemOpWidth::W8 => value,
    }
}

/// Compare `value1` and `value2` for equality, except the bytes identified by `addr` and `width`
/// may vary.
pub fn compare_except_bytes_at_offset<'a>(
    b: &Builder<'a>,
    value1: TWire<'a, u64>,
    value2: TWire<'a, u64>,
    addr: TWire<'a, u64>,
    width: MemOpWidth,
) -> TWire<'a, bool> {
    // Hard to write this as a function without const generics
    macro_rules! go {
        ($T:ty, $divisor:expr) => {{
            let value1_parts = bit_pack::split_bits::<[$T; WORD_BYTES / $divisor]>(b, value1.repr);
            let value2_parts = bit_pack::split_bits::<[$T; WORD_BYTES / $divisor]>(b, value2.repr);
            let offset = bit_pack::extract_low::<ByteOffset>(b, addr.repr);
            let mut acc = b.lit(true);
            for (idx, (&v1, &v2)) in value1_parts.iter().zip(value2_parts.iter()).enumerate() {
                let ignored = b.eq(offset, b.lit(ByteOffset::new(idx as u8 * $divisor)));
                acc = b.and(acc, b.mux(ignored, b.lit(true), b.eq(v1, v2)));
            }
            acc
        }};
    }

    match width {
        MemOpWidth::W1 => go!(u8, 1),
        MemOpWidth::W2 => go!(u16, 2),
        MemOpWidth::W4 => go!(u32, 4),
        MemOpWidth::W8 => b.lit(true),
    }
}

pub fn word_addr<'a>(
    b: &Builder<'a>,
    addr: TWire<'a, u64>,
) -> TWire<'a, WordAddr> {
    let (_offset, waddr) = *bit_pack::split_bits::<(ByteOffset, WordAddr)>(b, addr.repr);
    waddr
}
