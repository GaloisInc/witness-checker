use std::collections::HashMap;
use crate::eval::{self, CachingEvaluator};
use crate::ir::migrate::{self, Migrate};
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::Fetch;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::mem::{Memory, EquivSegments};
use crate::micro_ram::seg_graph::{SegGraphBuilder, SegGraphItem};
use crate::micro_ram::trace::{SegmentBuilder, Segment};
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
    segments_map: HashMap<usize, Segment<'a>>,
    segments: Vec<Option<Segment<'a>>>,
    seg_graph_live_edges: Vec<(usize, usize, RamState)>,

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
                b, &exec.segments, &exec.params, init_state),
            segments_map: HashMap::new(),
            segments: Vec::new(),
            seg_graph_live_edges: Vec::new(),

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
        self
    }

    fn run(mut self, b: &Builder<'a>, exec: &ExecBody) -> Self {
        for item in self.seg_graph_builder.get_order() {
            self.add_segment(b, exec, item);
            self = self;
        }

        // Segments are wrapped in `Option`, with `None` indicating unreachable segments for which
        // no circuit was generated.
        self.segments = (0 .. exec.segments.len()).map(|i| {
            self.segments_map.remove(&i)
        }).collect::<Vec<Option<_>>>();
        debug_assert!(self.segments_map.len() == 0);

        // Fill in advice and other secrets.

        let mut cycle = 0;
        let mut prev_state = self.init_state.clone();
        let mut prev_segment = None;
        for chunk in &exec.trace {
            if let Some(ref debug) = chunk.debug {
                if let Some(c) = debug.cycle {
                    cycle = c;
                }
                if let Some(ref s) = debug.prev_state {
                    prev_state = s.clone();
                }
                if debug.clear_prev_segment {
                    prev_segment = None;
                }
                if let Some(idx) = debug.prev_segment {
                    prev_segment = Some(idx);
                }
            }

            let seg = self.segments[chunk.segment].as_mut()
                .unwrap_or_else(|| panic!("trace uses unreachable segment {}", chunk.segment));
            assert_eq!(seg.idx, chunk.segment);
            seg.set_states(b, &exec.program, cycle, &prev_state, &chunk.states, &exec.advice);
            seg.check_states(&self.cx, b, cycle, self.check_steps, &chunk.states);

            if let Some(prev_segment) = prev_segment {
                self.seg_graph_live_edges.push(
                    (prev_segment, chunk.segment, prev_state.clone()));
            }
            prev_segment = Some(chunk.segment);

            cycle += chunk.states.len() as u32;
            if chunk.states.len() > 0 {
                prev_state = chunk.states.last().unwrap().clone();
                prev_state.cycle = cycle;
            }
        }

        self
    }

    fn add_segment(&mut self, b: &Builder<'a>, exec: &ExecBody, item: SegGraphItem) {
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

        let idx = match item {
            SegGraphItem::Segment(idx) => idx,
            SegGraphItem::Network => {
                self.seg_graph_builder.build_network(&b);
                return;
            },
        };

        let seg_def = &exec.segments[idx];
        let prev_state = self.seg_graph_builder.get_initial(&b, idx).clone();
        let prev_kmem = self.seg_graph_builder.take_initial_mem(idx);
        let (seg, kmem) = segment_builder.run(idx, seg_def, prev_state, prev_kmem);
        self.seg_graph_builder.set_final(idx, seg.final_state().clone());
        self.seg_graph_builder.set_final_mem(idx, kmem);
        assert!(!self.segments_map.contains_key(&idx));
        self.segments_map.insert(idx, seg);
    }

    fn finish(self, b: &Builder<'a>, _exec: &ExecBody) -> (Context<'a>, EquivSegments<'a>) {
        // This method is written in an unusual style to ensure that no unmigrated wires are left
        // dangling.  The only local variable allowed at top level is `x` - even `self` is consumed
        // as soon as possible so it can't be used later.  So the only data passed from one block
        // to the next is `x`, and `x` is always migrated as a unit.

        let x = {
            let mut eb = self;

            check_last(
                &eb.cx, b,
                eb.segments.last().unwrap().as_ref().unwrap().final_state(),
                eb.expect_zero,
            );

            let mut seg_graph = eb.seg_graph_builder.finish(&eb.cx, b);
            for (src, dest, state) in eb.seg_graph_live_edges {
                seg_graph.make_edge_live(b, src, dest, &state);
            }
            seg_graph.finish(b);

            // Explicitly drop anything that contains a `SecretHandle`, ensuring that defaults are
            // set before we move on.
            eb.segments.clear();

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
