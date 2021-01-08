
use clap::ArgMatches;
use crate::ir::typed::{TWire, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{
    Execution, RamInstr, RamState, RamStateRepr, MemPort, MemOpKind, Opcode, Advice,
};

pub mod if_mode;
pub mod tainted;

/*
mod leak_uninitialized;

// A checker mode and its respective state.
pub enum Mode<'a> {
    LeakUninitialized( leak_uninitialized::TaintState<'a>),
}

pub fn initialize<'a>(args: &'a ArgMatches, b: &Builder<'a>, exec: &'a Execution) -> Option<Mode<'a>> {
    match args.value_of("mode")? {
        "leak-uninitialized" => Some(Mode::LeakUninitialized(leak_uninitialized::initialize(&b, &exec))),
        m => {
            eprintln!("error: unknown mode `{}`", m);
            std::process::exit(1);
        }
    }
}

pub fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    // calc_im: &CalcIntermediate<'a>,
    mode: &mut Option<Mode<'a>>,
) {
    match mode {
        Some(Mode::LeakUninitialized(ts)) => {
            leak_uninitialized::check_step(cx, b, cycle, instr, mem_port, ts)
        },
        None => {},
    }
}

pub fn init_mem_taint<'a>(mode: &Option<Mode<'a>>) -> Option<u64> {
    // TODO
    unimplemented!{}
}

pub fn uses_tainted_mem<'a>(mode: &Option<Mode<'a>>) -> bool {
    // TODO
    unimplemented!{}
}
*/
