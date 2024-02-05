use std::collections::HashMap;
use log::info;
use zk_circuit_builder::ir::circuit::{Bits, Function};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{Builder, BuilderExt, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::seg_graph::{SegGraphBuilder, SegGraphItem};
use crate::micro_ram::trace::{self, SegmentBuilder, InstrLookup};
use crate::micro_ram::types::{ExecBody, RamState};
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness};
use super::{ExecBuilder, Common};


#[derive(Migrate)]
pub struct InstrTraceBuilder<'a> {
    calc_step_func: Function<'a>,
    calc_step_inner_cases: Vec<(Bits<'a>, Function<'a>)>,
    check_step_func: Function<'a>,
    seg_graph_builder: SegGraphBuilder<'a>,
    /// Map from segment index to the index of the trace chunk that uses that segment, along with
    /// the initial cycle of that chunk.  This is used in `add_segment` to initialize the secrets
    /// for the new segment (if that segment is actually used in the trace).
    seg_user_map: HashMap<usize, (usize, u32)>,
    debug_segment_graph_path: Option<String>,
}

impl<'a> InstrTraceBuilder<'a> {
    pub(super) fn new(
        b: &impl Builder<'a>,
        exec: &ExecBody,
        init_state: RamState,
        debug_segment_graph_path: Option<String>,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) -> InstrTraceBuilder<'a> {
        let calc_step_inner_cases = trace::define_calc_step_inner_cases(
            b, exec.params.privilege_levels);
        let it = exec.trace.as_instr();
        InstrTraceBuilder {
            calc_step_func: trace::define_calc_step_function(
                b,
                &calc_step_inner_cases,
                exec.params.num_regs,
                exec.params.privilege_levels,
            ),
            calc_step_inner_cases,
            check_step_func: trace::define_check_step_function(b),
            debug_segment_graph_path,
            seg_graph_builder: SegGraphBuilder::new(
                b, &it.segments, &exec.params, init_state, &it.chunks, project_witness),
            seg_user_map: HashMap::new(),
        }
    }

    pub(super) fn init(
        &mut self,
        c: &mut Common<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        seg_values: &[Vec<TWire<'a, u64>>],
    ) {
        if let Some(ref out_path) = self.debug_segment_graph_path {
            std::fs::write(out_path, self.seg_graph_builder.dump()).unwrap();
        }

        // Set up initial KnownMem
        let mut kmem = KnownMem::with_default(b.lit(0));
        for (seg, values) in exec.init_mem.iter().zip(seg_values.iter()) {
            kmem.init_segment(seg, &values);
        }
        self.seg_graph_builder.set_cpu_init_mem(kmem);
        debug_assert_eq!(seg_values.len(), exec.init_mem.len());

        // Populate `seg_user_map`.
        let mut cycle = 0;
        for (i, chunk) in exec.trace.as_instr().chunks.iter().enumerate() {
            if let Some(c) = chunk.debug.as_ref().and_then(|d| d.cycle) {
                cycle = c;
            }

            let old = self.seg_user_map.insert(chunk.segment, (i, cycle));
            assert!(old.is_none());

            cycle += chunk.states.len() as u32;
        }
    }

    pub(super) fn run(
        eb: &mut Rooted<'a, ExecBuilder<'a, Self>>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        let instr_lookup = InstrLookup::new(&exec.program);
        for item in eb.open(mh).t.seg_graph_builder.get_order() {
            match item {
                SegGraphItem::Segment(idx) => {
                    let mut eb = eb.open(mh);
                    let eb = &mut *eb;
                    eb.t.add_segment(&mut eb.c, b, exec, &instr_lookup, idx, project_witness);
                },
                SegGraphItem::Network => {
                    unsafe { mh.erase_and_migrate(b.circuit()) };
                    info!("seg_graph_builder.build_network");
                    let mut seg_graph_builder = eb.project(mh, |eb| &mut eb.t.seg_graph_builder);
                    SegGraphBuilder::build_network(&mut seg_graph_builder, mh, b, project_witness);
                    unsafe { mh.erase_and_migrate(b.circuit()) };
                    continue;
                },
            }

            unsafe { mh.erase_and_migrate(b.circuit()) };
        }
    }

    pub(super) fn add_segment(
        &mut self,
        c: &mut Common<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        instr_lookup: &InstrLookup,
        idx: usize,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        // Build the circuit for this segment.
        let mut segment_builder = SegmentBuilder {
            cx: &c.cx,
            b: b,
            ev: &mut c.ev,
            privilege_levels: c.privilege_levels,
            calc_step_func: self.calc_step_func,
            calc_step_inner_cases: &self.calc_step_inner_cases,
            check_step_func: self.check_step_func,
            mem: &mut c.mem,
            fetch: &mut c.fetch,
            params: &exec.params,
            prog: instr_lookup,
            check_steps: c.check_steps,
        };

        let seg_def = &exec.trace.as_instr().segments[idx];
        let mut prev_state = self.seg_graph_builder.get_initial(b, idx).clone();
        let prev_kmem = self.seg_graph_builder.take_initial_mem(idx);

        let external_advice_storage: [_; 2];
        let mut external_advice = None;

        if let Some(jump_dest) = seg_def.spontaneous_jump_pc() {
            let pc = prev_state.pc;
            let cycle = b.cast(prev_state.cycle);
            prev_state.pc = b.lit(jump_dest);
            external_advice_storage = [pc, cycle];
            external_advice = Some(&external_advice_storage as &[_]);
        }

        let (mut seg, kmem) = segment_builder.run(
            idx, seg_def, prev_state, prev_kmem, external_advice,
            move |w| {
                let ew = project_witness(w);
                &ew.trace.as_instr().segments[idx]
            });
        self.seg_graph_builder.set_final(idx, seg.final_state().clone());
        self.seg_graph_builder.set_final_mem(idx, kmem);

        // If this segment is actually used in the trace, find the relevant trace chunk and use its
        // data to initialize the segment's secrets.
        if let Some(&(chunk_idx, cycle)) = self.seg_user_map.get(&idx) {
            let chunk = &exec.trace.as_instr().chunks[chunk_idx];

            if c.check_steps > 0 {
                seg.check_states(&c.cx, b, cycle, c.check_steps, &chunk.states);
            }

            // FIXME: this leaks information, namely, the identity of the last used segment.  We
            // should either forbid mixing `--expect-zero` with public PC, or otherwise ensure that
            // this is only used for testing.
            if chunk_idx == exec.trace.as_instr().chunks.len() - 1 {
                super::check_last(&c.cx, b, seg.final_state(), c.expect_zero);
            }
        }
    }

    pub(super) fn finish(
        t: Rooted<'a, Self>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        cx: &mut Rooted<'a, Context<'a>>,
    ) {
        // Break apart `t` into pieces and re-root them.
        let InstrTraceBuilder { seg_graph_builder, .. } = t.take();
        let mut seg_graph_builder = mh.root(seg_graph_builder);

        info!("seg_graph_builder.finish");
        seg_graph_builder.take().finish(&cx.open(mh), b);
        unsafe { mh.erase_and_migrate(b.circuit()) };
    }
}
