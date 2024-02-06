use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{Builder, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::ExecBody;
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness};
use super::{ExecBuilder, TraceBuilder, Common};


#[derive(Migrate)]
pub struct BbmdTraceBuilder<'a> {
    _dummy: Option<zk_circuit_builder::ir::circuit::Wire<'a>>,
}

impl<'a> BbmdTraceBuilder<'a> {
    pub(super) fn new(
    ) -> BbmdTraceBuilder<'a> {
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
