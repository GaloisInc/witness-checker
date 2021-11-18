use std::collections::HashMap;
use crate::eval::{self, CachingEvaluator};
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::Fetch;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::mem::{Memory, EquivSegments};
use crate::micro_ram::seg_graph::{SegGraphBuilder, SegGraphItem};
use crate::micro_ram::trace::SegmentBuilder;
use crate::micro_ram::types::{ExecBody, RamState};


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
    ev: CachingEvaluator<'a, eval::Public>,
}

impl<'a> ExecBuilder<'a> {
    pub fn build(
        b: &Builder<'a>,
        cx: Context<'a>,
        exec: &ExecBody,
        exec_name: &str,
        equiv_segments: EquivSegments<'a>,
        init_state: RamState,
        check_steps: usize,
        expect_zero: bool,
        debug_segment_graph_path: Option<String>,
    ) -> (Context<'a>, EquivSegments<'a>) {
        let eb = ExecBuilder::new(
            b,
            cx,
            exec,
            equiv_segments,
            init_state,
            check_steps,
            expect_zero,
            debug_segment_graph_path,
        );
        let eb = eb.init(b, exec, exec_name);
        let eb = eb.run(b, exec);
        eb.finish(b, exec)
    }

    fn new(
        b: &Builder<'a>,
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

    fn init(mut self, b: &Builder<'a>, exec: &ExecBody, exec_name: &str) -> Self {
        if let Some(ref out_path) = self.debug_segment_graph_path {
            std::fs::write(out_path, self.seg_graph_builder.dump()).unwrap();
        }
        let mut kmem = KnownMem::with_default(b.lit(0));
        for seg in &exec.init_mem {
            let values = self.mem.init_segment(
                &b, seg, self.equiv_segments.exec_segments(exec_name));
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

        self
    }

    fn run(mut self, b: &Builder<'a>, exec: &ExecBody) -> Self {
        for item in self.seg_graph_builder.get_order() {
            match item {
                SegGraphItem::Segment(idx) => self.add_segment(b, exec, idx),
                SegGraphItem::Network => {
                    self.seg_graph_builder.build_network(&b);
                },
            }
            self = self;
        }

        self
    }

    fn add_segment(&mut self, b: &Builder<'a>, exec: &ExecBody, idx: usize) {
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
        let prev_state = self.seg_graph_builder.get_initial(&b, idx).clone();
        let prev_kmem = self.seg_graph_builder.take_initial_mem(idx);
        let (mut seg, kmem) = segment_builder.run(idx, seg_def, prev_state, prev_kmem);
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
            seg.set_states(b, &exec.program, cycle, prev_state, &chunk.states, &exec.advice);
            seg.check_states(&self.cx, b, cycle, self.check_steps, &chunk.states);

            if chunk_idx == exec.trace.len() - 1 {
                check_last(&self.cx, b, seg.final_state(), self.expect_zero);
            }
        }
    }

    fn finish(self, b: &Builder<'a>, _exec: &ExecBody) -> (Context<'a>, EquivSegments<'a>) {
        // This method is written in an unusual style to ensure that no unmigrated wires are left
        // dangling.  The only local variable allowed at top level is `x` - even `self` is consumed
        // as soon as possible so it can't be used later.  So the only data passed from one block
        // to the next is `x`, and `x` is always migrated as a unit.

        let x = {
            let eb = self;

            eb.seg_graph_builder.finish(&eb.cx, b);

            // Some consistency checks involve sorting, which requires that all the relevant
            // secrets be initialized first.
            eb.mem.assert_consistent(&eb.cx, b);
            eb.fetch.assert_consistent(&eb.cx, b);

            (eb.cx, eb.equiv_segments)
        };
        //let x = b.circuit().erase_and_migrate(x);

        x
    }
}

fn check_last<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
    expect_zero: bool,
) {
    let _g = b.scoped_label("check_last");
    let r0 = s.regs[0];
    if expect_zero {
        wire_assert!(
            cx, b.eq(r0, b.lit(0)),
            "final r0 is {} (expected {})",
            cx.eval(r0), 0,
        );
    }
}
