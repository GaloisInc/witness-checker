use std::collections::HashMap;
use log::info;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateContext, MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{Builder, BuilderExt, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::Fetch;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::mem::{Memory, EquivSegments};
use crate::micro_ram::seg_graph::{SegGraphBuilder, SegGraphItem};
use crate::micro_ram::trace::SegmentBuilder;
use crate::micro_ram::types::{ExecBody, RamState};
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness};


#[derive(Migrate)]
pub struct ExecBuilder<'a> {
    init_state: RamState,
    check_steps: usize,
    expect_zero: bool,
    debug_segment_graph_path: Option<String>,

    equiv_segments: EquivSegments<'a>,
    mem: Memory<'a>,
    fetch: Fetch<'a>,
    seg_graph_builder: SegGraphBuilder<'a>,
    /// Map from segment index to the index of the trace chunk that uses that segment, along with
    /// the initial cycle of that chunk.
    seg_user_map: HashMap<usize, (usize, u32)>,

    // These fields come last because they contain caches keyed on `Wire`s.  On migration, only
    // wires that were used during the migration of some previous field will be kept in the cache.
    cx: Context<'a>,
    ev: CachingEvaluator<'a, 'static, eval::Public>,
}

impl<'a> ExecBuilder<'a> {
    pub fn build(
        b: &impl Builder<'a>,
        mcx: &'a MigrateContext<'a>,
        cx: Context<'a>,
        exec: &ExecBody,
        exec_name: &'static str,
        equiv_segments: EquivSegments<'a>,
        init_state: RamState,
        check_steps: usize,
        expect_zero: bool,
        debug_segment_graph_path: Option<String>,
    ) -> (Context<'a>, EquivSegments<'a>) {
        let mut mh = MigrateHandle::new(mcx);
        let mh = &mut mh;

        let mut eb = mh.root(ExecBuilder::new(
            b, cx, exec, equiv_segments, init_state,
            check_steps, expect_zero, debug_segment_graph_path,
        ));
        eb.open(mh).init(b, exec, exec_name);
        ExecBuilder::run(&mut eb, mh, b, exec, move |w| &w.execs[exec_name]);
        eb.take().finish(mh, b, exec)
    }

    fn new(
        b: &impl Builder<'a>,
        cx: Context<'a>,
        exec: &ExecBody,
        equiv_segments: EquivSegments<'a>,
        init_state: RamState,
        check_steps: usize,
        expect_zero: bool,
        debug_segment_graph_path: Option<String>,
    ) -> ExecBuilder<'a> {
        ExecBuilder {
            init_state: init_state.clone(),
            check_steps,
            expect_zero,
            debug_segment_graph_path,

            equiv_segments,
            mem: Memory::new(),
            fetch: Fetch::new(b, &exec.program),
            seg_graph_builder: SegGraphBuilder::new(
                b, &exec.segments, &exec.params, init_state, &exec.trace),
            seg_user_map: HashMap::new(),

            cx,
            ev: CachingEvaluator::new()
        }
    }

    fn init(&mut self, b: &impl Builder<'a>, exec: &ExecBody, exec_name: &str) {
        if let Some(ref out_path) = self.debug_segment_graph_path {
            std::fs::write(out_path, self.seg_graph_builder.dump()).unwrap();
        }

        let mut kmem = KnownMem::with_default(b.lit(0));
        for seg in &exec.init_mem {
            let values = self.mem.init_segment(
                b, seg, self.equiv_segments.exec_segments(exec_name));
            kmem.init_segment(seg, &values);
        }
        self.seg_graph_builder.set_cpu_init_mem(kmem);

        let mut cycle = 0;
        for (i, chunk) in exec.trace.iter().enumerate() {
            if let Some(c) = chunk.debug.as_ref().and_then(|d| d.cycle) {
                cycle = c;
            }

            let old = self.seg_user_map.insert(chunk.segment, (i, cycle));
            assert!(old.is_none());

            cycle += chunk.states.len() as u32;
        }
    }

    fn run(
        this: &mut Rooted<'a, Self>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        for item in this.open(mh).seg_graph_builder.get_order() {
            match item {
                SegGraphItem::Segment(idx) =>
                    this.open(mh).add_segment(b, exec, idx, project_witness),
                SegGraphItem::Network => {
                    unsafe { mh.erase_and_migrate(b.circuit()) };
                    info!("seg_graph_builder.build_network");
                    let mut seg_graph_builder = this.project(mh, |eb| &mut eb.seg_graph_builder);
                    SegGraphBuilder::build_network(&mut seg_graph_builder, mh, b, project_witness);
                    unsafe { mh.erase_and_migrate(b.circuit()) };
                    continue;
                },
            }

            unsafe { mh.erase_and_migrate(b.circuit()) };
        }
    }

    fn add_segment(
        &mut self,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        idx: usize,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        let mut segment_builder = SegmentBuilder {
            cx: &self.cx,
            b: b,
            ev: &mut self.ev,
            mem: &mut self.mem,
            fetch: &mut self.fetch,
            params: &exec.params,
            prog: &exec.program,
            check_steps: self.check_steps,
        };

        let seg_def = &exec.segments[idx];
        let prev_state = self.seg_graph_builder.get_initial(b, idx).clone();
        let prev_kmem = self.seg_graph_builder.take_initial_mem(idx);
        let (mut seg, kmem) = segment_builder.run(idx, seg_def, prev_state, prev_kmem, move |w| {
            let ew = project_witness(w);
            &ew.segments[idx]
        });
        self.seg_graph_builder.set_final(idx, seg.final_state().clone());
        self.seg_graph_builder.set_final_mem(idx, kmem);

        if let Some(&(chunk_idx, cycle)) = self.seg_user_map.get(&idx) {
            let chunk = &exec.trace[chunk_idx];
            let debug_prev_state = chunk.debug.as_ref().and_then(|d| d.prev_state.as_ref());
            let prev_state = if let Some(s) = debug_prev_state {
                s
            } else if chunk_idx == 0 {
                &self.init_state
            } else {
                exec.trace[chunk_idx - 1].states.last().expect("empty chunk")
            };
            seg.check_states(&self.cx, b, cycle, self.check_steps, &chunk.states);

            if chunk_idx == exec.trace.len() - 1 {
                check_last(&self.cx, b, seg.final_state(), self.expect_zero);
            }
        }
    }

    fn finish(
        self,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        _exec: &ExecBody,
    ) -> (Context<'a>, EquivSegments<'a>) {
        let x = self;
        let mut cx = mh.root(x.cx);
        let mut equiv_segments = mh.root(x.equiv_segments);
        let mut seg_graph_builder = mh.root(x.seg_graph_builder);
        let mut mem = mh.root(x.mem);
        let mut fetch = mh.root(x.fetch);
        // Make sure no fields of `self`/`x` are used past this point.
        #[allow(unused)]
        let x = ();

        info!("seg_graph_builder.finish");
        seg_graph_builder.take().finish(&cx.open(mh), b);
        unsafe { mh.erase_and_migrate(b.circuit()) };

        info!("mem.assert_consistent");
        mem.take().assert_consistent(mh, &mut cx, b);
        unsafe { mh.erase_and_migrate(b.circuit()) };

        info!("fetch.assert_consistent");
        fetch.take().assert_consistent(mh, &mut cx, b);
        unsafe { mh.erase_and_migrate(b.circuit()) };

        (cx.take(), equiv_segments.take())
    }
}

fn check_last<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    s: &TWire<'a, RamState>,
    expect_zero: bool,
) {
    let _g = b.scoped_label("check_last");
    let r0 = s.regs[0];
    if expect_zero {
        wire_assert!(
            cx, b, b.eq(r0, b.lit(0)),
            "final r0 is {} (expected {})",
            cx.eval(r0), 0,
        );
    }
}
