//! Instruction-fetch consistency check.
//!
//! This includes setting up the program, adding `FetchPort`s for each cycle, sorting, and checking
//! the sorted list.
use std::convert::TryFrom;
use log::*;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::circuit::CircuitTrait;
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{TWire, Builder, BuilderExt, EvaluatorExt};
use crate::micro_ram::context::{Context, ContextEval};
use crate::micro_ram::types::{
    FetchPort, FetchPortRepr, PackedFetchPort, RamInstr, Opcode, CodeSegment, CompareFetchPort,
};
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness, SegmentWitness};
use zk_circuit_builder::routing::sort::{self, CompareLe};

#[derive(Migrate)]
pub struct Fetch<'a> {
    ports: Vec<TWire<'a, FetchPort>>,
    all_instrs: Vec<Vec<TWire<'a, RamInstr>>>,
    /// Default `addr` and `instr` values to use for uninitialized `FetchPort`s.  This corresponds
    /// to an actual instruction somewhere in the program, which means uninitialized `FetchPort`s
    /// will be valid under the normal rules, and no special checks for unused `FetchPort`s are
    /// necessary.
    default_addr_and_instr: (u64, RamInstr),
}

pub const PADDING_INSTR: RamInstr = RamInstr::new(Opcode::Answer, 0, 0, 0, true);

impl<'a> Fetch<'a> {
    pub fn new(
        b: &impl Builder<'a>,
        prog: &[CodeSegment],
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) -> Fetch<'a> {
        let num_ports = prog.iter().map(|cs| cs.len as usize).sum();
        let mut ports = Vec::with_capacity(num_ports);
        let mut all_instrs = Vec::with_capacity(prog.len());

        let mut first_public_instr = None;
        for (seg_idx, cs) in prog.iter().enumerate() {
            let mut seg_instrs = Vec::with_capacity(cs.len as usize);
            for i in 0 .. cs.len {
                let addr = cs.start + i;
                let instr: TWire<RamInstr> = if cs.secret {
                    b.secret_lazy(move |w: &MultiExecWitness| {
                        let w: &ExecWitness = project_witness(w);
                        w.init_fetch_instrs[seg_idx][usize::try_from(i).unwrap()]
                    })
                } else {
                    let instr = cs.instrs.get(i as usize).cloned()
                        .unwrap_or(PADDING_INSTR);
                    if first_public_instr.is_none() {
                        first_public_instr = Some((addr, instr));
                    }
                    b.lit(instr)
                };

                let fp = TWire::new(FetchPortRepr {
                    addr: b.lit(addr),
                    instr,
                    write: b.lit(true),
                });
                ports.push(fp);
                seg_instrs.push(instr);
            }
            all_instrs.push(seg_instrs);
        }

        Fetch {
            ports,
            all_instrs,
            default_addr_and_instr: first_public_instr
                .expect("program must contain at least one public instruction"),
        }
    }

    /// Get a `TWire<RamInstr>` for each instruction of each code segment.
    pub fn all_instrs(&self) -> &[Vec<TWire<'a, RamInstr>>] {
        &self.all_instrs
    }

    pub fn add_cycles<'b>(
        &mut self,
        b: &impl Builder<'a>,
        len: usize,
        project_witness: impl Fn(&MultiExecWitness) -> &SegmentWitness + Copy + 'static,
    ) -> CyclePorts<'a> {
        let mut cp = CyclePorts {
            ports: Vec::with_capacity(len),
        };

        let (default_addr, default_instr) = self.default_addr_and_instr;

        for i in 0 .. len {
            let addr = b.secret_lazy(move |w: &MultiExecWitness| {
                let w: &SegmentWitness = project_witness(w);
                if w.live() {
                    w.fetches[i].0
                } else {
                    default_addr
                }
            });
            let instr = b.secret_lazy(move |w: &MultiExecWitness| {
                let w: &SegmentWitness = project_witness(w);
                if w.live() {
                    w.fetches[i].1
                } else {
                    default_instr
                }
            });
            let write = b.lit(false);
            let fp = TWire::new(FetchPortRepr { addr, instr, write });
            cp.ports.push(CyclePort { fp });
        }

        self.ports.extend(cp.ports.iter().map(|p| p.fp));
        cp
    }

    /// Assert that this set of instruction fetch operations is internally consistent.
    ///
    /// This takes `self` by value to prevent adding more `FetchPort`s after the consistency check.
    pub fn assert_consistent(
        self,
        mh: &mut MigrateHandle<'a>,
        cx: &mut Rooted<'a, Context<'a>>,
        b: &impl Builder<'a>,
    ) {
        let (mut ports,) = {
            let Fetch { ports, all_instrs: _, default_addr_and_instr: _ } = self;
            (mh.root(ports),)
        };

        let mut sorted_ports = Rooted::new({
            let _g = b.scoped_label("fetch/sort");
            let mut sort = Rooted::new({
                let packed_ports = ports.open(mh).iter().map(|&fp| {
                    PackedFetchPort::from_unpacked(b, fp)
                }).collect::<Vec<_>>();
                sort::sort_by_key(b, &packed_ports, CompareLe, |w| {
                    let w = w.unpack(b);
                    b.cast::<_, CompareFetchPort>(w)
                })
            }, mh);

            while !sort.open(mh).is_ready() {
                sort.open(mh).step(b);
                unsafe { mh.erase_and_migrate(b.circuit()) };
            }

            let (packed_ports, sorted) = sort.take().finish(b);
            wire_assert!(cx = &cx.open(mh), b, sorted, "instruction fetch sorting failed");
            packed_ports.iter().map(|pfp| pfp.unpack(b)).collect::<Vec<_>>()
        }, mh);

        // Debug logging, showing the state before and after sorting.
        // TODO: need a way to run these prints during eval, with MultExecWitness available
        /*
        {
            let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
            let mut cev = ContextEval::new(b.circuit().as_base(), &mut ev);
            trace!("fetches:");
            for (i, port) in ports.open(mh).iter().enumerate() {
                trace!(
                    "fetch {:3}: {:5} {:x}, op{} {} {} {} {}",
                    i, cev.eval(port.write).0.map_or("??", |x| if !x { "read" } else { "write" }),
                    cev.eval(port.addr), cev.eval(port.instr.opcode), cev.eval(port.instr.dest),
                    cev.eval(port.instr.op1), cev.eval(port.instr.op2), cev.eval(port.instr.imm),
                );
            }
            trace!("sorted fetches:");
            for (i, port) in sorted_ports.open(mh).iter().enumerate() {
                trace!(
                    "fetch {:3}: {:5} {:x}, op{} {} {} {} {}",
                    i, cev.eval(port.write).0.map_or("??", |x| if !x { "read" } else { "write" }),
                    cev.eval(port.addr), cev.eval(port.instr.opcode), cev.eval(port.instr.dest),
                    cev.eval(port.instr.op1), cev.eval(port.instr.op2), cev.eval(port.instr.imm),
                );
            }
        }
        */

        // Run the consistency check.
        check_first_fetch(&cx.open(mh), b, sorted_ports.open(mh)[0]);

        for i in 1 .. sorted_ports.open(mh).len() {
            let cx = cx.open(mh);
            let sorted_ports = sorted_ports.open(mh);
            let port1 = sorted_ports[i - 1];
            let port2 = sorted_ports[i];
            check_fetch(&cx, b, port1, port2);

            if i % 10000 == 0 {
                unsafe { mh.erase_and_migrate(b.circuit()) };
            }
        }
    }
}

#[derive(Migrate)]
struct CyclePort<'a> {
    fp: TWire<'a, FetchPort>,
}

#[derive(Migrate)]
pub struct CyclePorts<'a> {
    ports: Vec<CyclePort<'a>>,
}

impl<'a> CyclePorts<'a> {
    pub fn get(&self, i: usize) -> TWire<'a, FetchPort> {
        self.ports[i].fp
    }

    pub fn get_instr(&self, i: usize) -> TWire<'a, RamInstr> {
        self.ports[i].fp.instr
    }

    pub fn iter<'b>(&'b self) -> impl Iterator<Item = TWire<'a, FetchPort>> + 'b {
        self.ports.iter().map(|p| p.fp)
    }
}


fn check_first_fetch<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    port: TWire<'a, FetchPort>,
) {
    let _g = b.scoped_label("fetch/check_first");
    wire_assert!(
        cx, b, port.write,
        "uninit fetch from program address {:x}",
        cx.eval(port.addr),
    );
}

fn check_fetch<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    port1: TWire<'a, FetchPort>,
    port2: TWire<'a, FetchPort>,
) {
    let _g = b.scoped_label("fetch/check");
    cx.when(b, b.not(port2.write), |cx| {
        wire_assert!(
            cx, b, b.eq(port2.addr, port1.addr),
            "fetch from uninitialized program address {:x}",
            cx.eval(port2.addr),
        );
        wire_assert!(
            cx, b, b.eq(port2.instr, port1.instr),
            "fetch from program address {:x} produced wrong instruction",
            cx.eval(port2.addr),
        );
    });
}
