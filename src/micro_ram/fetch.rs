//! Instruction-fetch consistency check.
//!
//! This includes setting up the program, adding `FetchPort`s for each cycle, sorting, and checking
//! the sorted list.
use log::*;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::circuit::CircuitTrait;
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{TWire, TSecretHandle, Builder, BuilderExt, EvaluatorExt};
use crate::micro_ram::context::{Context, ContextEval};
use crate::micro_ram::types::{
    FetchPort, FetchPortRepr, PackedFetchPort, RamInstr, CompareFetchPort,
};
use zk_circuit_builder::routing::sort::{self, CompareLe};

#[derive(Migrate)]
pub struct Fetch<'a> {
    ports: Vec<TWire<'a, FetchPort>>,
    /// Default value for secret `instr`s in uninitialized `FetchPort`s.
    default_instr: RamInstr,
}

impl<'a> Fetch<'a> {
    pub fn new(b: &impl Builder<'a>, prog: &[RamInstr]) -> Fetch<'a> {
        let mut ports = Vec::with_capacity(prog.len());

        for (i, instr) in prog.iter().enumerate() {
            let fp = b.lit(FetchPort {
                addr: i as u64,
                instr: instr.clone(),
                write: true,
            });
            ports.push(fp);
        }

        Fetch {
            ports,
            // Set the default `RamInstr` to the correct `RamInstr` for the default address (0).
            // This means uninitialized `FetchPort`s will be valid under the normal rules, and no
            // special checks for unused `FetchPort`s are necessary.
            default_instr: prog[0].clone(),
        }
    }

    pub fn add_cycles<'b>(
        &mut self,
        b: &impl Builder<'a>,
        len: usize,
    ) -> CyclePorts<'a> {
        let mut cp = CyclePorts {
            ports: Vec::with_capacity(len),
        };

        for _ in 0 .. len {
            let (addr, addr_secret) = b.secret();
            let (instr, instr_secret) = b.secret_default(self.default_instr.clone());
            let write = b.lit(false);
            let fp = TWire::new(FetchPortRepr { addr, instr, write });
            cp.ports.push(CyclePort { fp, addr_secret, instr_secret });
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
            let Fetch { ports, default_instr: _ } = self;
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
    addr_secret: TSecretHandle<'a, u64>,
    instr_secret: TSecretHandle<'a, RamInstr>,
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

    pub fn set(&self, b: &impl Builder<'a>, idx: usize, addr: u64, instr: RamInstr) {
        self.ports[idx].addr_secret.set(b, addr);
        self.ports[idx].instr_secret.set(b, instr);
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
