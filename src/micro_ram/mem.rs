//! Memory consistency check.
//!
//! This includes setting up initial memory, adding `MemPort`s for each cycle, sorting, and
//! checking the sorted list.
use log::*;
use crate::ir::typed::{TWire, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{
    MemPort, MemOpKind, PackedMemPort, Advice, MemSegment, MEM_PORT_PRELOAD_CYCLE,
    MEM_PORT_UNUSED_CYCLE,
};
use crate::sort;

pub struct Memory<'a> {
    verifier: bool,
    ports: Vec<TWire<'a, MemPort>>,
}

impl<'a> Memory<'a> {
    pub fn new(verifier: bool) -> Memory<'a> {
        Memory {
            verifier,
            ports: Vec::new(),
        }
    }

    pub fn init_segment(&mut self, b: &Builder<'a>, seg: &MemSegment) {
        self.ports.reserve(seg.len as usize);

        for i in 0 .. seg.len {
            let addr = seg.start + i;

            // Most of the MemPort is public.  Only the value is secret, if `seg.secret` is set.
            let mut mp = b.lit(MemPort {
                cycle: MEM_PORT_PRELOAD_CYCLE,
                addr,
                // Dummy value for now.  We fill in this field differently depending on `verifier`
                // and `seg.secret`.
                value: 0,
                op: MemOpKind::Write,
            });

            if self.verifier && seg.secret {
                mp.value = b.secret(None);
            } else {
                // `data` is implicitly zero-padded out to `seg.len`, to support `.bss`-style
                // zero-initialized segments.
                let value = seg.data.get(i as usize).cloned().unwrap_or(0);
                if seg.secret {
                    mp.value = b.secret(Some(value));
                } else {
                    mp.value = b.lit(value);
                }
            }

            self.ports.push(mp);
        }
    }

    pub fn add_cycles<'b>(
        &mut self,
        b: &Builder<'a>,
        len: usize,
        sparsity: usize,
        mut get_advice: impl FnMut(usize) -> (&'b [Advice], u32),
    ) -> CyclePorts<'a> {
        let num_ports = (len + sparsity - 1) / sparsity;

        let mut cp = CyclePorts {
            ports: Vec::with_capacity(num_ports),
            sparsity,
        };

        if self.verifier {
            // Simple case: everything is secret.
            for _ in 0 .. num_ports {
                cp.ports.push(b.secret(None));
            }
            self.ports.extend_from_slice(&cp.ports);
            return cp;
        }

        for i in 0 .. num_ports {
            // Find the `MemOp` advice in this block (if any) and build the mem port.
            let mut mp = None;
            let mut old_j = 0;
            for j in i * sparsity .. (i + 1) * sparsity {
                let (advs, cycle) = get_advice(j);
                for adv in advs {
                    if let Advice::MemOp { addr, value, op } = *adv {
                        assert!(
                            mp.is_none(),
                            "multiple mem ports in block {}: cycle {}, cycle {}",
                            i, old_j, j,
                        );
                        old_j = j;
                        mp = Some(MemPort { cycle, addr, value, op });
                    }
                }
            }

            let mp = mp.unwrap_or_else(|| MemPort {
                cycle: MEM_PORT_UNUSED_CYCLE,
                // We want all in-use `MemPort`s to be distinct, since it simplifies checking the
                // correspondence between `MemPort`s and steps.  We make unused ports distinct too,
                // so we can just check that all ports are distinct.
                addr: (self.ports.len() + i) as u64,
                value: 0,
                op: MemOpKind::Write,
            });

            cp.ports.push(b.secret(Some(mp)));
        }

        self.ports.extend_from_slice(&cp.ports);
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
        check_first_mem(&cx, &b, &sorted_ports[0]);
        let it = sorted_ports.iter().zip(sorted_ports.iter().skip(1)).enumerate();
        for (i, (port1, port2)) in it {
            check_mem(&cx, &b, i, port1, port2);
        }
    }
}

pub struct CyclePorts<'a> {
    ports: Vec<TWire<'a, MemPort>>,
    sparsity: usize,
}

impl<'a> CyclePorts<'a> {
    pub fn get(&self, i: usize) -> TWire<'a, MemPort> {
        self.ports[i / self.sparsity]
    }
}


/// Check that memory operation `port` is valid as the first memory op.
fn check_first_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    port: &TWire<'a, MemPort>,
) {
    let _g = b.scoped_label("check_first_mem");
    // If the first memory port is active, then it must not be a read, since there are no previous
    // writes to read from.
    let active = b.ne(port.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));
    wire_bug_if!(
        cx, b.mux(active, b.eq(port.op, b.lit(MemOpKind::Read)), b.lit(false)),
        "uninit read from {:x} on cycle {}",
        cx.eval(port.addr), cx.eval(port.cycle),
    );
}

/// Check that memory operation `port2` can follow operation `port1`.
fn check_mem<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    index: usize,
    port1: &TWire<'a, MemPort>,
    port2: &TWire<'a, MemPort>,
) {
    let _g = b.scoped_label(format_args!("check_mem/index {}", index));
    let active = b.ne(port2.cycle, b.lit(MEM_PORT_UNUSED_CYCLE));

    // Whether `port2` is the first memory op for its address.
    let is_first = b.or(
        b.ne(port1.addr, port2.addr),
        b.eq(port1.cycle, b.lit(MEM_PORT_UNUSED_CYCLE)),
    );

    cx.when(b, b.and(active, b.not(is_first)), |cx| {
        cx.when(b, b.eq(port1.op, b.lit(MemOpKind::Poison)), |cx| {
            let is_poison = b.eq(port2.op, b.lit(MemOpKind::Poison));

            // Poison -> Poison is invalid.
            wire_assert!(
                cx, b.not(is_poison),
                "double poison of address {:x} on cycle {}",
                cx.eval(port2.addr), cx.eval(port2.cycle),
            );

            // Poison -> Read/Write is a bug.
            wire_bug_if!(
                cx, b.not(is_poison),
                "access of poisoned address {:x} on cycle {}",
                cx.eval(port2.addr), cx.eval(port2.cycle),
            );
        });

        // A Read must have the same value as the previous Read/Write.  (Write and Poison values
        // are unconstrained.)
        cx.when(b, b.eq(port2.op, b.lit(MemOpKind::Read)), |cx| {
            wire_assert!(
                cx, b.eq(port1.value, port2.value),
                "read from {:x} on cycle {} produced {} (expected {})",
                cx.eval(port2.addr), cx.eval(port2.cycle),
                cx.eval(port2.value), cx.eval(port1.value),
            );
        });
    });

    cx.when(b, b.and(active, is_first), |cx| {
        // The first operation for an address can't be a Read, since there is no previous Write for
        // it to read from.
        wire_assert!(
            cx, b.ne(port2.op, b.lit(MemOpKind::Read)),
            "uninit read from {:x} on cycle {}",
            cx.eval(port2.addr), cx.eval(port2.cycle),
        );
    });
}

