use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{Builder, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::trace::InstrLookup;
use crate::micro_ram::types::{ExecBody, Opcode};
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness};
use super::{ExecBuilder, TraceBuilder, Common};


#[derive(Migrate)]
pub struct BbmdTraceBuilder<'a> {
    _dummy: Option<zk_circuit_builder::ir::circuit::Wire<'a>>,
}

impl<'a> BbmdTraceBuilder<'a> {
    pub(super) fn new(
        b: &impl Builder<'a>,
        exec: &ExecBody,
    ) -> BbmdTraceBuilder<'a> {
        let bt = exec.trace.as_bbmd();
        let instrs = InstrLookup::new(&exec.program);

        // Count the maximum number of advice inputs used in any block.
        let mut max_mem_ports = 0;
        let mut max_advise = 0;
        for block in &bt.blocks {
            let mut counts = AdviceCounts::default();
            for pc in block.iter_pcs() {
                count_opcode_advice_inputs(instrs[pc].opcode(), &mut counts);
            }

            let AdviceCounts { mem_ports, advise } = counts;
            if mem_ports > max_mem_ports {
                max_mem_ports = mem_ports;
            }
            if advise > max_advise {
                max_advise = advise;
            }
        }

        eprintln!("max mem ports = {}", max_mem_ports);
        eprintln!("max advise = {}", max_advise);

        BbmdTraceBuilder {
            _dummy: None,
        }
    }
}

impl<'a> TraceBuilder<'a> for BbmdTraceBuilder<'a> {
    fn init(
        &mut self,
        c: &mut Common<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        seg_values: &[Vec<TWire<'a, u64>>],
    ) {
    }

    fn run(
        eb: &mut Rooted<'a, ExecBuilder<'a, Self>>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        todo!()
    }

    fn finish(
        t: Rooted<'a, Self>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        cx: &mut Rooted<'a, Context<'a>>,
    ) {
        // Break apart `t` into pieces and re-root them.
        let BbmdTraceBuilder { .. } = t.take();
    }
}

#[derive(Clone, Debug, Default)]
struct AdviceCounts {
    mem_ports: usize,
    advise: usize,
}

fn count_opcode_advice_inputs(
    opcode: Opcode,
    counts: &mut AdviceCounts,
) {
    match opcode {
        Opcode::And |
        Opcode::Or |
        Opcode::Xor |
        Opcode::Not |
        Opcode::Add |
        Opcode::Sub |
        Opcode::Mull |
        Opcode::Umulh |
        Opcode::Smulh |
        Opcode::Udiv |
        Opcode::Umod |
        Opcode::Shl |
        Opcode::Shr => {},

        Opcode::Cmpe |
        Opcode::Cmpa |
        Opcode::Cmpae |
        Opcode::Cmpg |
        Opcode::Cmpge => {},

        Opcode::Mov |
        Opcode::Cmov => {},

        Opcode::Jmp |
        Opcode::Cjmp |
        Opcode::Cnjmp => {},

        Opcode::Store1 |
        Opcode::Store2 |
        Opcode::Store4 |
        Opcode::Store8 |
        Opcode::Load1 |
        Opcode::Load2 |
        Opcode::Load4 |
        Opcode::Load8 |
        Opcode::Poison8 => {
            counts.mem_ports += 1;
        },

        Opcode::Read => panic!("Opcode::Read is unsupported"),
        Opcode::Answer => {},

        Opcode::Advise => {
            counts.advise += 1;
        },

        Opcode::Sink1 |
        Opcode::Taint1 => {},

        Opcode::Stutter => {},
    }
}
