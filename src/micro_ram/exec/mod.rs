use std::collections::HashMap;
use log::info;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::hash::sha256::Sha256;
use zk_circuit_builder::ir::circuit::{Bits, Function};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateContext, MigrateHandle, Rooted};
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
    ExecBuilder::run(&mut eb, mh, b, exec, move |w| &w.execs[exec_name]);
    eb.take().finish(mh, b, exec)
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
        let calc_step_inner_cases = trace::define_calc_step_inner_cases(b, exec.params.privilege_levels);
        let it = exec.trace.as_instr();
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
            t: InstrTraceBuilder {
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
            },
        }
    }

    fn init(
        &mut self, b: &impl Builder<'a>, exec: &ExecBody, exec_name: &'static str) {
        if let Some(ref out_path) = self.t.debug_segment_graph_path {
            std::fs::write(out_path, self.t.seg_graph_builder.dump()).unwrap();
        }

        // Set up initial KnownMem
        let mut kmem = KnownMem::with_default(b.lit(0));
        let mut seg_values = Vec::with_capacity(exec.init_mem.len());
        for (i, seg) in exec.init_mem.iter().enumerate() {
            let values = self.c.mem.init_segment(
                b,
                i,
                seg,
                self.c.equiv_segments.exec_segments(exec_name),
                move |w| &w.execs[exec_name],
            );
            kmem.init_segment(seg, &values);
            seg_values.push(values);
        }
        self.t.seg_graph_builder.set_cpu_init_mem(kmem);
        debug_assert_eq!(seg_values.len(), exec.init_mem.len());

        // Populate `seg_user_map`.
        let mut cycle = 0;
        for (i, chunk) in exec.trace.as_instr().chunks.iter().enumerate() {
            if let Some(c) = chunk.debug.as_ref().and_then(|d| d.cycle) {
                cycle = c;
            }

            let old = self.t.seg_user_map.insert(chunk.segment, (i, cycle));
            assert!(old.is_none());

            cycle += chunk.states.len() as u32;
        }

        // Add extra `MemPort`s to enforce `expect_write`.
        if let Some(addr) = self.c.expect_write {
            // We write a 0 before execution begins, and try to read back a 1 after the program
            // terminates.  This succeeds only if the program overwrites the 0 with a 1 during its
            // execution.  We can't simply leave the memory uninitialized because reads from
            // uninitialized memory are allowed (and the value produced is unconstrained).
            self.c.mem.add_initial_write(b, addr, 0);
            self.c.mem.add_final_read(b, addr, 1);
        }

        // Add hash check for the `commitment`.
        if let Some(commitment) = exec.params.commitment {
            let _g = b.scoped_label("check commitment");
            match commitment {
                Commitment::Sha256(expect_hash) => {
                    let mut h = Sha256::new(b);

                    for (cs, instrs) in exec.program.iter().zip(self.c.fetch.all_instrs().iter()) {
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
                        cx = &self.c.cx, b, b.eq(actual_hash, b.lit(expect_hash)),
                        "bad commitment: actual hash is {:?}, but expected {:?}",
                        cx.eval(actual_hash), expect_hash,
                    );
                },
            }
        }
    }

    fn run(
        this: &mut Rooted<'a, Self>,
        mh: &mut MigrateHandle<'a>,
        b: &impl Builder<'a>,
        exec: &ExecBody,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        let instr_lookup = InstrLookup::new(&exec.program);
        for item in this.open(mh).t.seg_graph_builder.get_order() {
            match item {
                SegGraphItem::Segment(idx) =>
                    this.open(mh).add_segment(b, exec, &instr_lookup, idx, project_witness),
                SegGraphItem::Network => {
                    unsafe { mh.erase_and_migrate(b.circuit()) };
                    info!("seg_graph_builder.build_network");
                    let mut seg_graph_builder = this.project(mh, |eb| &mut eb.t.seg_graph_builder);
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
        instr_lookup: &InstrLookup,
        idx: usize,
        project_witness: impl Fn(&MultiExecWitness) -> &ExecWitness + Copy + 'static,
    ) {
        // Build the circuit for this segment.
        let mut segment_builder = SegmentBuilder {
            cx: &self.c.cx,
            b: b,
            ev: &mut self.c.ev,
            privilege_levels: self.c.privilege_levels,
            calc_step_func: self.t.calc_step_func,
            calc_step_inner_cases: &self.t.calc_step_inner_cases,
            check_step_func: self.t.check_step_func,
            mem: &mut self.c.mem,
            fetch: &mut self.c.fetch,
            params: &exec.params,
            prog: instr_lookup,
            check_steps: self.c.check_steps,
        };

        let seg_def = &exec.trace.as_instr().segments[idx];
        let mut prev_state = self.t.seg_graph_builder.get_initial(b, idx).clone();
        let prev_kmem = self.t.seg_graph_builder.take_initial_mem(idx);

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
        self.t.seg_graph_builder.set_final(idx, seg.final_state().clone());
        self.t.seg_graph_builder.set_final_mem(idx, kmem);

        // If this segment is actually used in the trace, find the relevant trace chunk and use its
        // data to initialize the segment's secrets.
        if let Some(&(chunk_idx, cycle)) = self.t.seg_user_map.get(&idx) {
            let chunk = &exec.trace.as_instr().chunks[chunk_idx];

            if self.c.check_steps > 0 {
                seg.check_states(&self.c.cx, b, cycle, self.c.check_steps, &chunk.states);
            }

            // FIXME: this leaks information, namely, the identity of the last used segment.  We
            // should either forbid mixing `--expect-zero` with public PC, or otherwise ensure that
            // this is only used for testing.
            if chunk_idx == exec.trace.as_instr().chunks.len() - 1 {
                check_last(&self.c.cx, b, seg.final_state(), self.c.expect_zero);
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
        let mut cx = mh.root(x.c.cx);
        let mut equiv_segments = mh.root(x.c.equiv_segments);
        let mut seg_graph_builder = mh.root(x.t.seg_graph_builder);
        let mut mem = mh.root(x.c.mem);
        let mut fetch = mh.root(x.c.fetch);
        // Make sure no fields of `self`/`x` are used past this point.
        #[allow(unused)]
        let x = ();

        // Force a GC here to ensure that temporaries from the last few segments are flushed.  This
        // prevents having temporaries from those segments and temporaries from the various
        // permutations live at the same time.
        unsafe { mh.force_erase_and_migrate(b.circuit()) };

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
