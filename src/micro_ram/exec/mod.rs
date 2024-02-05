use std::collections::HashMap;
use log::info;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::hash::sha256::Sha256;
use zk_circuit_builder::ir::circuit::{Bits, Function};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateContext, MigrateHandle, Rooted, Projected};
use zk_circuit_builder::ir::typed::{Builder, BuilderExt, TWire};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::Fetch;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::mem::{Memory, EquivSegments};
use crate::micro_ram::seg_graph::{SegGraphBuilder, SegGraphItem};
use crate::micro_ram::trace::{self, SegmentBuilder, InstrLookup};
use crate::micro_ram::types::{Commitment, ExecBody, RamState, RamInstrRepr, Opcode};
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness};


#[derive(Migrate)]
struct Common<'a> {
    init_state: RamState,
    check_steps: usize,
    /// If set, then the trace is valid only if the final value of `r0` is 0.
    expect_zero: bool,
    /// If set, then the trace is valid only if the program writes a 1 to this address before
    /// terminating.
    expect_write: Option<u64>,
    /// If set, then the trace is invalid if low-privilege code (bit 31 of the PC is 0) accesses
    /// high-privilege memory (bit 31 of the address is 1) or jumps to high-privilege code.
    privilege_levels: bool,

    equiv_segments: EquivSegments<'a>,
    mem: Memory<'a>,
    fetch: Fetch<'a>,

    // These fields come last because they contain caches keyed on `Wire`s.  On migration, only
    // wires that were used during the migration of some previous field will be kept in the cache.
    cx: Context<'a>,
    ev: CachingEvaluator<'a, 'static, eval::Public>,
}

#[derive(Migrate)]
struct InstrTraceBuilder<'a> {
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

#[derive(Migrate)]
struct ExecBuilder<'a, TB> {
    /// Trace builder
    t: TB,

    // `Common` must come last to ensure a specific migration order - see comment in `Common` for
    // details.
    c: Common<'a>,
}

pub fn build<'a>(
    b: &impl Builder<'a>,
    mcx: &'a MigrateContext<'a>,
    cx: Context<'a>,
    exec: &ExecBody,
    exec_name: &'static str,
    equiv_segments: EquivSegments<'a>,
    init_state: RamState,
    check_steps: usize,
    expect_zero: bool,
    expect_write: Option<u64>,
    debug_segment_graph_path: Option<String>,
) -> (Context<'a>, EquivSegments<'a>) {
    let mut mh = MigrateHandle::new(mcx);
    let mh = &mut mh;

    let mut eb = mh.root(ExecBuilder::new(
        b, cx, exec, equiv_segments, init_state,
        check_steps, expect_zero, expect_write, debug_segment_graph_path,
        move |w| &w.execs[exec_name],
    ));
    eb.open(mh).init(b, exec, exec_name);
    InstrTraceBuilder::run(
        &mut eb, mh, b, exec,
        move |w| &w.execs[exec_name],
    );
    ExecBuilder::finish(eb, mh, b)
}

impl<'a> ExecBuilder<'a, InstrTraceBuilder<'a>> {
    fn new(
        b: &impl Builder<'a>,
        cx: Context<'a>,
        exec: &ExecBody,
        equiv_segments: EquivSegments<'a>,
        init_state: RamState,
        check_steps: usize,
        expect_zero: bool,
        expect_write: Option<u64>,
        debug_segment_graph_path: Option<String>,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) -> ExecBuilder<'a, InstrTraceBuilder<'a>> {
        ExecBuilder {
            c: Common {
                init_state: init_state.clone(),
                check_steps,
                expect_zero,
                expect_write,
                privilege_levels: exec.params.privilege_levels,
                equiv_segments,
                mem: Memory::new(),
                fetch: Fetch::new(b, &exec.program, project_witness),
                cx,
                ev: CachingEvaluator::new()
            },
            t: InstrTraceBuilder::new(
               b,
               exec,
               init_state,
               debug_segment_graph_path,
               project_witness,
            ),
        }
    }

    fn init(&mut self, b: &impl Builder<'a>, exec: &ExecBody, exec_name: &'static str) {
        let mut seg_values = Vec::with_capacity(exec.init_mem.len());
        for (i, seg) in exec.init_mem.iter().enumerate() {
            let values = self.c.mem.init_segment(
                b,
                i,
                seg,
                self.c.equiv_segments.exec_segments(exec_name),
                move |w| &w.execs[exec_name],
            );
            seg_values.push(values);
        }

        self.c.init(b, exec, &seg_values);
        self.t.init(&mut self.c, b, exec, &seg_values);
    }

    fn finish(
        eb: Rooted<'a, Self>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
    ) -> (Context<'a>, EquivSegments<'a>) {
        // Break apart `eb` into pieces and re-root them.
        let ExecBuilder { c, t } = eb.take();
        let c = mh.root(c);
        let t = mh.root(t);

        // Force a GC here to ensure that temporaries from the last few segments are flushed.  This
        // prevents having temporaries from those segments and temporaries from the various
        // permutations live at the same time.
        unsafe { mh.force_erase_and_migrate(b.circuit()) };

        let (mut cx, equiv_segments) = Common::finish(c, mh, b);

        InstrTraceBuilder::finish(t, mh, b, &mut cx);

        (cx.take(), equiv_segments.take())
    }
}

impl<'a> Common<'a> {
    fn init(
        &mut self,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        seg_values: &[Vec<TWire<'a, u64>>],
    ) {
        // Add extra `MemPort`s to enforce `expect_write`.
        if let Some(addr) = self.expect_write {
            // We write a 0 before execution begins, and try to read back a 1 after the program
            // terminates.  This succeeds only if the program overwrites the 0 with a 1 during its
            // execution.  We can't simply leave the memory uninitialized because reads from
            // uninitialized memory are allowed (and the value produced is unconstrained).
            self.mem.add_initial_write(b, addr, 0);
            self.mem.add_final_read(b, addr, 1);
        }

        // Add hash check for the `commitment`.
        if let Some(commitment) = exec.params.commitment {
            let _g = b.scoped_label("check commitment");
            match commitment {
                Commitment::Sha256(expect_hash) => {
                    let mut h = Sha256::new(b);

                    for (cs, instrs) in exec.program.iter().zip(self.fetch.all_instrs().iter()) {
                        if !cs.secret || cs.uncommitted {
                            continue;
                        }
                        for instr in instrs {
                            let RamInstrRepr { opcode, dest, op1, op2, imm } = instr.repr;
                            h.push(b, opcode);
                            h.push(b, dest);
                            h.push(b, op1);
                            h.push(b, op2);
                            h.push(b, imm);
                        }
                    }

                    for (seg, values) in exec.init_mem.iter().zip(seg_values.iter()) {
                        if !seg.secret || seg.uncommitted {
                            continue;
                        }
                        for &w in values {
                            h.push(b, w);
                        }
                    }

                    let actual_hash = h.finish(b);
                    wire_assert!(
                        cx = &self.cx, b, b.eq(actual_hash, b.lit(expect_hash)),
                        "bad commitment: actual hash is {:?}, but expected {:?}",
                        cx.eval(actual_hash), expect_hash,
                    );
                },
            }
        }
    }

    fn finish(
        c: Rooted<'a, Self>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
    ) -> (
        Rooted<'a, Context<'a>>,
        Rooted<'a, EquivSegments<'a>>,
    ) {
        // Break apart `c` into pieces and re-root them.
        let Common { equiv_segments, mem, fetch, cx, .. } = c.take();
        let mut equiv_segments = mh.root(equiv_segments);
        let mut mem = mh.root(mem);
        let mut fetch = mh.root(fetch);
        let mut cx = mh.root(cx);

        info!("mem.assert_consistent");
        mem.take().assert_consistent(mh, &mut cx, b);
        unsafe { mh.erase_and_migrate(b.circuit()) };

        info!("fetch.assert_consistent");
        fetch.take().assert_consistent(mh, &mut cx, b);
        unsafe { mh.erase_and_migrate(b.circuit()) };

        (cx, equiv_segments)
    }
}

impl<'a> InstrTraceBuilder<'a> {
    fn new(
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

    fn init(
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

    fn run(
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

    fn add_segment(
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
                check_last(&c.cx, b, seg.final_state(), c.expect_zero);
            }
        }
    }

    fn finish(
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
