
use clap::ArgMatches;
use crate::ir::typed::{TWire, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{
    Execution, RamInstr, RamState, RamStateRepr, MemPort, MemOpKind, Opcode, Advice,
};

pub mod if_mode;
pub mod tainted;

