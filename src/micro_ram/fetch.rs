//! Instruction-fetch consistency check.
//!
//! This includes setting up the program, adding `FetchPort`s for each cycle, sorting, and checking
//! the sorted list.
use log::*;
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{TWire, TSecretHandle, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{FetchPort, FetchPortRepr, PackedFetchPort, RamInstr};
use crate::routing::sort;

#[derive(Migrate)]
pub struct Fetch<'a> {
    ports: Vec<TWire<'a, FetchPort>>,
    /// Default value for secret `instr`s in uninitialized `FetchPort`s.
    default_instr: RamInstr,
}

impl<'a> Fetch<'a> {
    pub fn new(b: &Builder<'a>, prog: &[RamInstr]) -> Fetch<'a> {
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
        b: &Builder<'a>,
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
    pub fn assert_consistent(self, cx: &Context<'a>, b: &Builder<'a>) {
        let sorted_ports = {
            let _g = b.scoped_label("sort fetch");
            let mut packed_ports = self.ports.iter().map(|&fp| {
                PackedFetchPort::from_unpacked(&b, fp)
            }).collect::<Vec<_>>();
            let sorted = sort::sort(&b, &mut packed_ports, &mut |&x, &y| b.le(x, y));
            wire_assert!(&cx, sorted, "instruction fetch sorting failed");
            packed_ports.iter().map(|pfp| pfp.unpack(&b)).collect::<Vec<_>>()
        };

        // Debug logging, showing the state before and after sorting.
        trace!("fetches:");
        for (i, port) in self.ports.iter().enumerate() {
            trace!(
                "fetch {:3}: {:5} {:x}, op{} {} {} {} {}",
                i, cx.eval(port.write).0.map_or("??", |x| if !x { "read" } else { "write" }),
                cx.eval(port.addr), cx.eval(port.instr.opcode), cx.eval(port.instr.dest),
                cx.eval(port.instr.op1), cx.eval(port.instr.op2), cx.eval(port.instr.imm),
            );
        }
        trace!("sorted fetches:");
        for (i, port) in sorted_ports.iter().enumerate() {
            trace!(
                "fetch {:3}: {:5} {:x}, op{} {} {} {} {}",
                i, cx.eval(port.write).0.map_or("??", |x| if !x { "read" } else { "write" }),
                cx.eval(port.addr), cx.eval(port.instr.opcode), cx.eval(port.instr.dest),
                cx.eval(port.instr.op1), cx.eval(port.instr.op2), cx.eval(port.instr.imm),
            );
        }

        // Run the consistency check.
        check_first_fetch(cx, b, sorted_ports[0]);
        let it = sorted_ports.iter().zip(sorted_ports.iter().skip(1)).enumerate();
        for (i, (&port1, &port2)) in it {
            check_fetch(cx, b, i, port1, port2);
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

    pub fn set(&self, b: &Builder<'a>, idx: usize, addr: u64, instr: RamInstr) {
        self.ports[idx].addr_secret.set(b, addr);
        self.ports[idx].instr_secret.set(b, instr);
    }
}


fn check_first_fetch<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    port: TWire<'a, FetchPort>,
) {
    let _g = b.scoped_label("check_first_fetch");
    wire_assert!(
        cx, port.write,
        "uninit fetch from program address {:x}",
        cx.eval(port.addr),
    );
}

fn check_fetch<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    index: usize,
    port1: TWire<'a, FetchPort>,
    port2: TWire<'a, FetchPort>,
) {
    let _g = b.scoped_label(format_args!("check_fetch/index {}", index));
    cx.when(b, b.not(port2.write), |cx| {
        wire_assert!(
            cx, b.eq(port2.addr, port1.addr),
            "fetch from uninitialized program address {:x}",
            cx.eval(port2.addr),
        );
        wire_assert!(
            cx, b.eq(port2.instr, port1.instr),
            "fetch from program address {:x} produced wrong instruction",
            cx.eval(port2.addr),
        );
    });
}
