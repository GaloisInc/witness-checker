//! Memory consistency check.
//!
//! This includes setting up initial memory, adding `MemPort`s for each cycle, sorting, and
//! checking the sorted list.
use std::cell::RefCell;
use std::cmp;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::iter;
use std::rc::Rc;
use log::*;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::gadget::bit_pack;
use zk_circuit_builder::ir::circuit::{CircuitTrait, CircuitExt};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{
    TWire, TSecretHandle, Builder, BuilderExt, Flatten, EvaluatorExt,
};
use zk_circuit_builder::routing::sort::{self, CompareLt};
use crate::micro_ram::context::{Context, ContextEval};
use crate::micro_ram::types::{
    MemPort, MemOpKind, MemOpWidth, PackedMemPort, MemSegment, ByteOffset, WordAddr,
    MemoryEquivalence, MEM_PORT_PRELOAD_CYCLE, MEM_PORT_UNUSED_CYCLE, WORD_BOTTOM, WORD_BYTES,
    CompareMemPort,
};
use crate::mode::if_mode::IfMode;
use crate::mode::tainted;

use zk_circuit_builder::ir::migrate::{self, Migrate};

#[derive(Migrate)]
pub struct Memory<'a> {
    ports: Vec<TWire<'a, MemPort>>,
    unused: Unused,
}

#[derive(Clone, Debug, Default)]
struct Unused(Rc<RefCell<Vec<bool>>>);

impl<'a> Memory<'a> {
    pub fn new() -> Memory<'a> {
        Memory {
            ports: Vec::new(),
            unused: Unused::default(),
        }
    }

    /// Add `MemPort`s for initializing `seg`.  Returns wires carrying the value of each word in
    /// the segment.
    pub fn init_segment(
        &mut self,
        b: &impl Builder<'a>,
        seg: &MemSegment,
        mut exec_equivs: ExecSegments<'a, '_>,
    ) -> Vec<TWire<'a, u64>> {
        let mut unused = self.unused.0.borrow_mut();
        self.ports.reserve(seg.len as usize);
        unused.reserve(seg.len as usize);
        let mut value_wires = Vec::with_capacity(seg.len as usize);
        
        // Get the values of the word.  `data` is implicitly zero-padded out to
        // `seg.len`, to support `.bss`-style zero-initialized segments.  For secret segments
        // in verifier mode, `seg.data` is always empty, so the `value` is zero (but unused).
        let values:Vec<u64> = (0..seg.len).map(|i| seg.data.get(i as usize).cloned().unwrap_or(0)).collect(); 

        // Then create the wires. Depends on whether the
        // segment is part of an qeuivalence class
        let mem_wires = match exec_equivs.get(&seg.name) {
            // If the segmetn is not in an equivalence class
            // just build new wires depending on whether the
            // segment is secret or not
            ExecSegment::NoEquiv => if seg.secret {
                values.iter().map(|&value| b.secret_init(|| value)).collect()
            } else {
                values.iter().map(|&value| b.lit(value)).collect()
            },

            //TODO: check equality with supplied values.
            ExecSegment::Equiv(wires) => wires.to_owned(),

            ExecSegment::NeedsInit(wires) => {
                // all memory equivalences must be on secret segments
                assert!(seg.secret);
                *wires = values.iter().map(|&value| b.secret_init(|| value)).collect();
                wires.clone()
            },
        };

        // Then create the memports 
        for (i, mem_wire) in mem_wires.iter().enumerate() {
            // Initial memory values are given in terms of words, not bytes.
            let waddr = seg.start + (i as u64);

            // Most of the MemPort is public.  Only the value is secret, if `seg.secret` is set.
            let mut mp = b.lit(MemPort {
                cycle: MEM_PORT_PRELOAD_CYCLE,
                addr: waddr * MemOpWidth::WORD.bytes() as u64,
                value: 0,
                op: MemOpKind::Write,
                tainted: IfMode::new(|pf| seg.tainted.as_ref().unwrap(&pf).get(i as usize).cloned().unwrap_or(WORD_BOTTOM)),
                width: MemOpWidth::WORD,
            });

            mp.value = *mem_wire;

            value_wires.push(mp.value);
            self.ports.push(mp);
            unused.push(false);
        }

        value_wires
    }

    pub fn add_cycles<'b>(
        &mut self,
        cx: &Context<'a>,
        b: &impl Builder<'a>,
        len: usize,
        sparsity: usize,
    ) -> CyclePorts<'a> {
        let len = u32::try_from(len).unwrap();
        let sparsity_u8 = u8::try_from(sparsity).unwrap();
        self.add_cycles_common(cx, b, len, (0..len).step_by(sparsity).map(|start| {
            (start, (cmp::min(len, start + sparsity_u8 as u32) - start) as u8)
        }))
    }

    pub fn add_cycles_irregular<'b>(
        &mut self,
        cx: &Context<'a>,
        b: &impl Builder<'a>,
        len: usize,
        idxs: impl IntoIterator<Item = usize>,
    ) -> CyclePorts<'a> {
        let len = u32::try_from(len).unwrap();
        self.add_cycles_common(cx, b, len, idxs.into_iter().map(|idx| {
            (u32::try_from(idx).unwrap(), 1)
        }))
    }

    fn add_cycles_common<'b>(
        &mut self,
        cx: &Context<'a>,
        b: &impl Builder<'a>,
        cycles_len: u32,
        ranges: impl IntoIterator<Item = (u32, u8)>,
    ) -> CyclePorts<'a> {
        let mut cp = CyclePorts {
            port_starts: Vec::new(),
            ports: Vec::new(),
            unused: self.unused.clone(),
            unused_offset: self.unused.0.borrow().len(),
        };

        let ranges = ranges.into_iter();
        cp.port_starts.reserve(ranges.size_hint().0 + 1);
        cp.ports.reserve(ranges.size_hint().0);

        for (i, (start, port_len)) in ranges.enumerate() {
            // For correctness, no SparseMemPort should have a valid range that extends beyond
            // `0..cycles_len`.
            assert!(start.checked_add(port_len as u32).unwrap() <= cycles_len);
            cp.port_starts.push(start);

            let (mp, mp_secret) = b.secret_default(MemPort {
                cycle: MEM_PORT_UNUSED_CYCLE,
                // We want all in-use `MemPort`s to be distinct, since it simplifies checking the
                // correspondence between `MemPort`s and steps.  We make unused ports distinct too,
                // so we can just check that all ports are distinct.
                addr: (self.ports.len() + i) as u64 * MemOpWidth::WORD.bytes() as u64,
                value: 0,
                op: MemOpKind::Write,
                tainted: IfMode::new(|_fp| WORD_BOTTOM),
                width: MemOpWidth::WORD,
            });
            let (user, user_secret) = b.secret_default(0);
            cp.ports.push(SparseMemPort {
                mp, mp_secret,
                user, user_secret,
                max_candidate_users: port_len,
                public_non_users: 0,
                is_set: false,
            });
        }
        cp.port_starts.push(cycles_len);

        assert!((1 .. cp.port_starts.len()).all(|i| cp.port_starts[i - 1] < cp.port_starts[i]));

        cp.assert_valid(cx, b);
        self.ports.extend(cp.ports.iter().map(|smp| smp.mp));
        self.unused.0.borrow_mut().extend(iter::repeat(false).take(cp.ports.len()));
        cp
    }

    /// Assert that this set of memory operations is internally consistent.
    ///
    /// This takes `self` by value to prevent adding more `MemPort`s after the consistency check.
    pub fn assert_consistent(
        self,
        mh: &mut MigrateHandle<'a>,
        cx: &mut Rooted<'a, Context<'a>>,
        b: &impl Builder<'a>,
    ) {
        let (mut ports, unused): (_, Vec<bool>) = {
            let Memory { ports, unused } = self;
            let unused = unused.0.borrow();
            (mh.root(ports), unused.clone())
        };
        assert_eq!(ports.open(mh).len(), unused.len());

        // Sort the memory ports by addres and then by cycle.  Most of the ordering logic is
        // handled by the `typed::Lt` impl for `PackedMemPort`.
        let mut sorted_ports = Rooted::new({
            let _g = b.scoped_label("mem/sort");
            let mut sort = Rooted::new({
                let packed_ports = ports.open(mh).iter().zip(unused.iter())
                    .filter_map(|(mp, &unused)| if unused { None } else { Some(mp) })
                    .map(|&mp| PackedMemPort::from_unpacked(b, mp))
                    .collect::<Vec<_>>();
                // Using `lt` instead of `le` for the comparison here means the sortedness check will
                // also ensure that every `MemPort` is distinct.
                sort::sort_by_key(b, &packed_ports, CompareLt, |w| {
                    let w = w.unpack(b);
                    b.cast::<_, CompareMemPort>(w)
                })
            }, mh);

            while !sort.open(mh).is_ready() {
                sort.open(mh).step(b);
                unsafe { mh.erase_and_migrate(b.circuit()) };
            }

            let (packed_ports, sorted) = sort.take().finish(b);
            wire_assert!(cx = &cx.open(mh), b, sorted, "memory op sorting failed");
            packed_ports.iter().map(|pmp| pmp.unpack(b)).collect::<Vec<_>>()
        }, mh);

        // Debug logging, showing the state before and after sorting.
        // TODO: need a way to run these prints during eval, with MultExecWitness available
        /*
        {
            let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
            let mut cev = ContextEval::new(b.circuit().as_base(), &mut ev);
            trace!("mem ops:");
            for (i, (port, &unused)) in ports.open(mh).iter().zip(unused.iter()).enumerate() {
                if unused {
                    trace!("mem op {:3}: unused", i);
                } else {
                    trace!(
                        "mem op {:3}: op{}, {:x}, value {}, cycle {}",
                        i, cev.eval(port.op.repr), cev.eval(port.addr), cev.eval(port.value),
                        cev.eval(port.cycle),
                    );
                }
            }
            trace!("sorted mem ops:");
            for (i, port) in sorted_ports.open(mh).iter().enumerate() {
                trace!(
                    "mem op {:3}: op{}, {:x}, value {}, cycle {}",
                    i, cev.eval(port.op.repr), cev.eval(port.addr), cev.eval(port.value),
                    cev.eval(port.cycle),
                );
            }
        }
        */

        // Run the consistency check.
        // The first port has no previous port.  Supply a dummy port and set `prev_valid = false`.
        if sorted_ports.open(mh).len() > 0 {
            let cx = cx.open(mh);
            let sorted_ports = sorted_ports.open(mh);
            check_mem(&cx, b, &sorted_ports[0], b.lit(false), sorted_ports[0]);
        }

        for i in 1 .. sorted_ports.open(mh).len() {
            let cx = cx.open(mh);
            let sorted_ports = sorted_ports.open(mh);
            let prev = &sorted_ports[i - 1];
            let port = sorted_ports[i];

            let prev_valid = b.eq(word_addr(b, prev.addr), word_addr(b, port.addr));
            check_mem(&cx, b, prev, prev_valid, port);

            unsafe { mh.erase_and_migrate(b.circuit()) };
        }
    }
}

impl<'a, 'b> Migrate<'a, 'b> for Unused {
    type Output = Unused;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, _v: &mut V) -> Unused {
        self.clone()
    }
}

#[derive(Default, Migrate)]
pub struct EquivSegments<'a> {
    /// Data for each equivalence class.  The entry is `None` if no member of the class has been
    /// processed yet, and otherwise is `Some(words)`.
    data: Vec<Option<Vec<TWire<'a, u64>>>>,
    /// Map from execution name to segment name to equivalence class index.  The resulting index
    /// can be used to look up the equivalence class in `data`.
    equivs: HashMap<String, HashMap<String, usize>>,
}

impl<'a> EquivSegments<'a> {
    pub fn new(mem_equivs: &[MemoryEquivalence]) -> EquivSegments<'a> {
        let mut es = EquivSegments {
            data: vec![None; mem_equivs.len()],
            equivs: HashMap::new(),
        };

        for (i, mem_eq) in mem_equivs.iter().enumerate() {
            for (exec_name, seg) in mem_eq.iter() {
                let exec_equivs = es.equivs.entry(exec_name.to_owned())
                    .or_insert_with(|| HashMap::new());
                exec_equivs.insert(seg.to_owned(), i);
            }
        }

        es
    }

    pub fn exec_segments(&mut self, seg_name: &str) -> ExecSegments<'a, '_> {
        ExecSegments {
            data: &mut self.data,
            seg_map: self.equivs.get(seg_name),
        }
    }
}

/// Helper type for looking up the equivalence classes and initializers for segments in a
/// particular execution.
pub struct ExecSegments<'a, 'b> {
    data: &'b mut [Option<Vec<TWire<'a, u64>>>],
    seg_map: Option<&'b HashMap<String, usize>>,
}

pub enum ExecSegment<'a, 'b> {
    /// The segment is not a member of an equivalence class.
    NoEquiv,
    /// The segment is a member of an equivalence class, and has already been initialized.
    Equiv(&'b [TWire<'a, u64>]),
    /// The segment is a member of an equivalence class, and needs to be initialized because this
    /// is the first use.
    NeedsInit(&'b mut Vec<TWire<'a, u64>>),
}

impl<'a, 'b> ExecSegments<'a, 'b> {
    pub fn get(&mut self, name: &str) -> ExecSegment<'a, '_> {
        let opt_index = self.seg_map.as_ref().and_then(|m| m.get(name).cloned());
        let index = match opt_index {
            Some(x) => x,
            None => return ExecSegment::NoEquiv,
        };

        if self.data[index].is_some() {
            ExecSegment::Equiv(self.data[index].as_ref().unwrap())
        } else {
            self.data[index] = Some(Vec::new());
            ExecSegment::NeedsInit(self.data[index].as_mut().unwrap())
        }
    }
}

/// A `MemPort` that is potentially shared by several steps.
#[derive(Clone, Migrate)]
pub struct SparseMemPort<'a> {
    mp: TWire<'a, MemPort>,
    /// Which of the steps actually uses this `MemPort`.  If no step uses it, the value will be out
    /// of range (`>= sparsity`).
    user: TWire<'a, u8>,
    mp_secret: TSecretHandle<'a, MemPort>,
    user_secret: TSecretHandle<'a, u8>,

    /// Number of cycles that can use this port.  For secret segments, this is equal to the
    /// sparsity (or slightly less for the last port, if the sparsity doesn't evenly divide the
    /// segment length.)
    ///
    /// If `user` is less than `max_candidate_users`, then this memory port is in use.
    max_candidate_users: u8,
    /// Bitmask of cycles that are covered by `max_candidate_users` but are publicly known not to
    /// use this memory port.  If bit `i` is set, then `user` is publicly known not to equal `i`.
    public_non_users: u64,

    is_set: bool,
}

impl<'a> SparseMemPort<'a> {
    /// Check whether `user` could possibly be the user of this port.  If this method returns
    /// `false`, then `self.user` is guaranteed not to equal `user`.
    fn is_candidate_user(&self, user: u8) -> bool {
        if user >= self.max_candidate_users {
            return false;
        }
        if let Some(mask) = 1_u64.checked_shl(user as u32) {
            if self.public_non_users & mask != 0 {
                return false;
            }
        }
        true
    }

    /// Count how many values `self.user` can possibly take on.
    fn num_candidate_users(&self) -> u8 {
        self.max_candidate_users - self.public_non_users.count_ones() as u8
    }

    fn set_unused_by(&mut self, user: u8) {
        debug_assert!(user < self.max_candidate_users);
        if let Some(mask) = 1_u64.checked_shl(user as u32) {
            self.public_non_users |= mask;
        }
    }
}

#[derive(Migrate)]
pub struct CyclePorts<'a> {
    /// The initial cycle covered by each port in `ports`.  `ports[i]` handles cycles in the range
    /// `port_starts[i] .. port_starts[i+1]`.  We keep an extra trailing element in `port_starts`
    /// to indicate the length (number of cycles covered) of the last port.
    port_starts: Vec<u32>,
    ports: Vec<SparseMemPort<'a>>,

    unused: Unused,
    unused_offset: usize,
}

impl<'a> CyclePorts<'a> {
    /// Returns the port index and the user number within that port for cycle `i`.  If there is no
    /// port that covers cycle `i`, this returns `None`.
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
        let smp = &self.ports[idx];
        let user = i - self.port_starts[idx];
        if user >= smp.max_candidate_users as u32 {
            return None;
        }
        let user = user as u8;
        if !smp.is_candidate_user(user) {
            return None;
        }
        Some((idx, user as u8))
    }

    /// Get the `MemPort` used by step `i`.  Returns `MemPort::default()` if step `i` does not have
    /// a `MemPort` assigned to it.
    ///
    /// For correctness, it's important that calling `get(i)` for every `0 <= i < len` (where `len`
    /// is the length passed to `add_cycles_irregular`) will produce every in-use `MemPort`.  This
    /// method achieves that by returning every port in `ports` aside from those that are publicly
    /// known to be unused (`num_candidate_users() == 0`).
    pub fn get(&self, b: &impl Builder<'a>, i: usize) -> TWire<'a, MemPort> {
        let (idx, user) = match self.index_to_port(u32::try_from(i).unwrap()) {
            Some(x) => x,
            // `None` means no port covers step `i`.
            None => return b.lit(MemPort::default()),
        };

        if self.ports[idx].num_candidate_users() == 1 {
            // Avoid an extra mux when sparsity is disabled.
            return self.ports[idx].mp;
        }

        let smp = &self.ports[idx];
        b.mux(
            b.eq(smp.user, b.lit(user as u8)),
            smp.mp,
            b.lit(MemPort::default()),
        )
    }

    /// Initialize the `MemPort` for `i` with the values in `port`.  `i` is the index of a cycle,
    /// not a port, so it can range up to `self.ports.len() * self.sparsity` (the number of cycles
    /// covered by this `CyclePorts`), not just `self.ports.len()` (the number of actual ports).
    pub fn set_port(&mut self, b: &impl Builder<'a>, i: usize, port: MemPort) {
        let (idx, user) = self.index_to_port(u32::try_from(i).unwrap())
            .unwrap_or_else(|| panic!("no memory port is available for index {}", i));
        let smp = &mut self.ports[idx];
        assert!(!smp.is_set, "multiple mem ops require sparse mem port {}", idx);
        smp.mp_secret.set(b, port);
        smp.user_secret.set(b, user);
        smp.is_set = true;
    }

    /// Record that cycle `i` is publicly known not to use its `MemPort`.
    pub fn set_unused(&mut self, i: usize) {
        if let Some((idx, user)) = self.index_to_port(u32::try_from(i).unwrap()) {
            let smp = &mut self.ports[idx];
            debug_assert!(smp.is_candidate_user(user));
            // Rather than handle interactions between `set_port` and `set_unused` on the same
            // port, we just require all `set_unused` calls to happen first.
            assert!(!smp.is_set,
                "marked cycle {} unused, but its sparse mem port {} is already used", i, idx);
            smp.set_unused_by(user);
            if smp.num_candidate_users() == 0 {
                smp.is_set = true;
                self.unused.0.borrow_mut()[self.unused_offset + idx] = true;
            }
        }
    }

    pub fn has_port(&self, i: usize) -> bool {
        self.index_to_port(u32::try_from(i).unwrap()).is_some()
    }

    pub fn iter<'b>(&'b self) -> impl Iterator<Item = SparseMemPort<'a>> + 'b {
        self.ports.iter().cloned()
    }

    /// Perform validity checks, as described in `docs/memory_sparsity.md`.
    fn assert_valid(&self, cx: &Context<'a>, b: &impl Builder<'a>) {
        for (i, smp) in self.ports.iter().enumerate() {
            if smp.num_candidate_users() == 0 {
                // This needs no assertion.  The port is publicly known to be unused, so we ensure
                // `smp.mp` is omitted from the memory checker.

                // FIXME: temporary assertion until the above is implemented
                wire_assert!(
                    cx, b, b.eq(smp.mp.cycle, b.lit(MEM_PORT_UNUSED_CYCLE)),
                    "block {} must be unused, as it has no candidate users",
                    i,
                );

                continue;
            }

            if smp.num_candidate_users() == 1 {
                // This needs no assertion.  `get` returns this port without consulting `user`, so
                // the value of `user` doesn't matter.
                continue;
            }

            // The number of candidate users is usually very small (<5), so a bunch of `or`s is
            // probably faster than converting to bits for an `lt`.
            let mut acc = b.eq(smp.mp.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));
            for user in 0..smp.max_candidate_users {
                if smp.is_candidate_user(user) {
                    acc = b.or(acc, b.eq(smp.user, b.lit(user)));
                }
            }

            {
                let user = smp.user;
                let max = smp.max_candidate_users;
                let mask = smp.public_non_users;
                wire_assert!(
                    cx, b, acc,
                    "block {} user index {} is invalid (max {}, excluded mask {:b})",
                    i, cx.eval(user), max, mask,
                );
            }
        }
    }
}


/// Get the "misalignment" of an address, equal to `addr % width.bytes()`.  The result is zero for
/// well-aligned addresses.
fn addr_misalignment<'a>(
    _cx: &Context<'a>,
    b: &impl Builder<'a>,
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
    b: &impl Builder<'a>,
    prev: &TWire<'a, MemPort>,
    prev_valid: TWire<'a, bool>,
    port: TWire<'a, MemPort>,
) {
    let _g = b.scoped_label("mem/check");
    let active = b.ne(port.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));

    // Alignment: `addr` must be a multiple of `width.bytes()`.
    let misalign = addr_misalignment(cx, b, port.addr, port.width);
    wire_assert!(
        cx, b, b.eq(misalign, b.lit(ByteOffset::new(0))),
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
                cx, b, b.not(is_poison),
                "double poison of address {:x} on cycle {}",
                cx.eval(port.addr), cx.eval(port.cycle),
            );

            // Poison -> Read/Write is a bug.
            wire_bug_if!(
                cx, b, b.not(is_poison),
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
            cx, b, b.eq(port.value, prev_value),
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
        let offset = bit_pack::extract_low::<ByteOffset>(b, port.addr.repr);
        for w in MemOpWidth::iter() {
            let mostly_eq = compare_except_bytes_at_offset(
                b,
                port.value,
                prev_value,
                offset,
                w,
            );
            mostly_eq_acc = b.mux(
                b.eq(port.width, b.lit(w)),
                mostly_eq,
                mostly_eq_acc,
            );
        }
        wire_assert!(
            cx, b, mostly_eq_acc,
            "{:?} to {:x} on cycle {} modified outside width {:?}: 0x{:x} != 0x{:x}",
            cx.eval(port.op), cx.eval(port.addr), cx.eval(port.cycle), cx.eval(port.width),
            cx.eval(port.value), cx.eval(prev_value),
        );

        tainted::check_write_memports(cx, b, &prev_taint, &port, &offset);
    });
}


/// Extract `width` bytes from `value`, starting at the offset indicated by the low bits of `addr`.
/// The result is zero-extended to 64 bits.
pub fn extract_bytes_at_offset<'a>(
    b: &impl Builder<'a>,
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
    b: &impl Builder<'a>,
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
    b: &impl Builder<'a>,
    value1: TWire<'a, u64>,
    value2: TWire<'a, u64>,
    offset: TWire<'a, ByteOffset>,
    width: MemOpWidth,
) -> TWire<'a, bool> {
    // Hard to write this as a function without const generics
    macro_rules! go {
        ($T:ty, $divisor:expr) => {{
            let value1_parts = bit_pack::split_bits::<[$T; WORD_BYTES / $divisor]>(b, value1.repr);
            let value2_parts = bit_pack::split_bits::<[$T; WORD_BYTES / $divisor]>(b, value2.repr);
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
    b: &impl Builder<'a>,
    addr: TWire<'a, u64>,
) -> TWire<'a, WordAddr> {
    let (_offset, waddr) = *bit_pack::split_bits::<(ByteOffset, WordAddr)>(b, addr.repr);
    waddr
}
