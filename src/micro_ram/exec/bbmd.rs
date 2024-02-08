use std::cmp;
use zk_circuit_builder::ir::circuit::{
    CircuitTrait, CircuitExt, Wire, Function, DefineFunction, SwitchCase, Ty,
};
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::migrate::handle::{MigrateHandle, Rooted};
use zk_circuit_builder::ir::typed::{
    self, Builder, BuilderExt, BuilderImpl, TWire, FromWireList, ToWireList,
};
use crate::micro_ram::context::Context;
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::trace::{self, InstrLookup};
use crate::micro_ram::types::{ExecBody, Opcode, BbmdBlock, RamState, MemPort, Params};
use crate::micro_ram::witness::{MultiExecWitness, ExecWitness};
use super::{ExecBuilder, TraceBuilder, Common};


pub struct BbmdTraceBuilder<'a> {
    /// Number of advice arguments taken by each block function.
    counts: AdviceCounts,
    block_functions: Vec<Function<'a>>,
    no_op_function: Function<'a>,
    switch_cases: &'a [SwitchCase<'a>],
}

impl<'a, 'b> Migrate<'a, 'b> for BbmdTraceBuilder<'a> {
    type Output = BbmdTraceBuilder<'b>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> BbmdTraceBuilder<'b> {
        let switch_cases = self.switch_cases.iter().map(|&case| v.visit(case)).collect::<Vec<_>>();
        let switch_cases = v.new_circuit().switch_case_list(&switch_cases);

        BbmdTraceBuilder {
            counts: self.counts,
            block_functions: v.visit(self.block_functions),
            no_op_function: v.visit(self.no_op_function),
            switch_cases,
        }
    }
}

impl<'a> BbmdTraceBuilder<'a> {
    pub(super) fn new(
        b: &impl Builder<'a>,
        exec: &ExecBody,
    ) -> BbmdTraceBuilder<'a> {
        let bt = exec.trace.as_bbmd();
        let instrs = InstrLookup::new(&exec.program);

        // Count the maximum number of advice inputs used in any block.
        let mut max_counts = AdviceCounts::default();
        for block in &bt.blocks {
            let mut counts = AdviceCounts::default();
            for pc in block.iter_pcs() {
                count_opcode_advice_inputs(instrs[pc].opcode(), &mut counts);
            }
            max_counts.max_assign(counts);
        }

        eprintln!("max mem ports = {}", max_counts.mem_ports);
        eprintln!("max advise = {}", max_counts.advise);

        // Generate a function for each block
        let mut block_functions = Vec::with_capacity(bt.blocks.len());
        for (i, block) in bt.blocks.iter().enumerate() {
            block_functions.push(define_block_function(
                b,
                &instrs,
                &max_counts,
                &exec.params,
                i,
                &block,
            ));
        }


        // Generate a list of switch cases
        let mut switch_cases = Vec::with_capacity(bt.blocks.len() + 1);
        for (i, &bf) in block_functions.iter().enumerate() {
            let pattern = b.circuit().bits(Ty::uint(32), i as u32);
            let body = bf;
            let case = b.circuit().switch_case::<MultiExecWitness, (), _>(
                pattern,
                body,
                &[],
                |_, _, _| (&()).into(),
            );
            switch_cases.push(case);
        }

        let no_op_function = define_no_op_block_function(b, &max_counts, &exec.params);
        let no_op_case = b.circuit().switch_case::<MultiExecWitness, (), _>(
            b.circuit().bits(Ty::uint(32), bt.blocks.len() as u32),
            no_op_function,
            &[],
            |_, _, _| (&()).into(),
        );
        switch_cases.push(no_op_case);

        let switch_cases = b.circuit().switch_case_list(&switch_cases);

        BbmdTraceBuilder {
            counts: max_counts,
            block_functions,
            no_op_function,
            switch_cases,
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
        let mut eb = mh.open(eb);
        let eb = &mut *eb;
        let cx = &mut eb.c.cx;
        let bt = exec.trace.as_bbmd();
        let counts = eb.t.counts.clone();
        let check_steps = eb.c.check_steps;
        let no_op_block_idx = bt.blocks.len() as u32;
        let switch_cases = eb.t.switch_cases;

        let mut s = b.lit(eb.c.init_state.clone());
        for idx in 0 .. exec.params.trace_len.unwrap() {
            let choice = b.secret_lazy(move |w| {
                let ew = project_witness(w);
                let bt_w = ew.trace.as_bbmd();
                match bt_w.chunks.get(idx) {
                    Some(cw) => cw.block_idx as u32,
                    // Past the end of the trace, use the special no-op block function.
                    None => no_op_block_idx,
                }
            });

            let num_mem_ports = counts.mem_ports;
            let mem_ports = eb.c.mem.add_mem_ports(b, counts.mem_ports, move |w| {
                let ew = project_witness(w);
                let bt_w = ew.trace.as_bbmd();
                let cw = match bt_w.chunks.get(idx) {
                    Some(x) => x,
                    None => return &[],
                };
                &cw.mem_ports
            });

            let num_advice_values = counts.advise;
            let advice_values = b.secret_lazy_sized(&[num_advice_values], move |w| {
                let ew = project_witness(w);
                let bt_w = ew.trace.as_bbmd();

                let mut v = Vec::with_capacity(num_advice_values);
                if let Some(cw) = bt_w.chunks.get(idx) {
                    v.extend(cw.advice_values.iter().cloned());
                }
                v.resize(num_advice_values, 0);
                v
            });

            let args = (s, mem_ports, advice_values);
            let (arg_wires, _arg_sizes) = typed::to_wire_list(&TWire::<BlockFnArgs>::new(args));
            let arg_wires = b.circuit().wire_list(&arg_wires);

            let switch_result = b.circuit().switch(choice.repr, switch_cases, arg_wires);

            let sizes = [exec.params.num_regs];
            let num_results = BlockFnResult::expected_num_wires(&mut sizes.iter().copied());
            let result_wires = (0 .. num_results).map(|i| {
                b.circuit().extract(switch_result, i)
            }).collect::<Vec<_>>();
            let results = typed::from_wire_list::<BlockFnResult>(
                b.circuit().as_base(), &result_wires, &sizes);
            let (new_s, asserts, bugs) = results.repr;

            if check_steps > 0 {
                // We can't check individual step results since they aren't returned from the block
                // functions.  Instead, if any checking was requested, we check the output of every
                // switch.
                if let Some(chunk) = bt.chunks.get(idx) {
                    let expect = chunk.states.last().unwrap().clone();
                    let cycle_post = bt.chunks[..idx + 1].iter()
                        .map(|c| c.states.len()).sum::<usize>() ;
                    // `check_state` expects the cycle number and the post state of the
                    // corresponding step.  Cycle N takes `state.cycle` from `N` to `N+1`.
                    let cycle_pre = cycle_post - 1;
                    trace::check_state(cx, b, idx, cycle_pre as u32, &new_s, &b.lit(expect));
                }
            }

            s = new_s;

            wire_assert!(cx, b, asserts, "assertion failed in block {}", idx);
            wire_bug_if!(cx, b, bugs, "bug detected in block {}", idx);
        }
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

#[derive(Clone, Copy, Debug, Default, Migrate)]
struct AdviceCounts {
    mem_ports: usize,
    advise: usize,
}

impl AdviceCounts {
    fn max(self, other: AdviceCounts) -> AdviceCounts {
        AdviceCounts {
            mem_ports: cmp::max(self.mem_ports, other.mem_ports),
            advise: cmp::max(self.advise, other.advise),
        }
    }

    fn max_assign(&mut self, other: AdviceCounts) {
        *self = self.max(other);
    }
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

type BlockFnArgs = (
    RamState,
    Vec<MemPort>,
    Vec<u64>,
);

type BlockFnResult = (
    RamState,
    bool, bool,
);

fn define_block_function<'a>(
    b: &impl Builder<'a>,
    instrs: &InstrLookup,
    counts: &AdviceCounts,
    params: &Params,
    block_idx: usize,
    block: &BbmdBlock,
) -> Function<'a> {
    struct BlockFunction<'b> {
        instrs: &'b InstrLookup<'b>,
        counts: &'b AdviceCounts,
        block: &'b BbmdBlock,
        block_idx: usize,
        num_regs: usize,
        privilege_levels: bool,
    }

    impl<'a, 'b> DefineFunction<'a> for BlockFunction<'b> {
        fn build_body<C>(self, c: &C, args_wires: &[Wire<'a>]) -> Wire<'a>
        where C: CircuitTrait<'a> {
            let sizes = [self.num_regs, self.counts.mem_ports, self.counts.advise];
            let args = typed::from_wire_list::<BlockFnArgs>(c.as_base(), &args_wires, &sizes);
            let (s0, mem_ports, advise_values) = args.repr;

            let cx = Context::new(c);
            let b = BuilderImpl::from_ref(c);
            let mut ev = CachingEvaluator::<eval::Public>::new();
            let block_idx = self.block_idx;

            let expect_pc0 = self.block.iter_pcs().next()
                .unwrap_or_else(|| panic!("block {} has empty pcs list?", self.block_idx));
            let actual_pc0 = s0.pc;
            wire_assert!(cx, b, b.eq(actual_pc0, b.lit(expect_pc0)),
                "block {}: bad initial pc {} (expected {})",
                block_idx, cx.eval(actual_pc0), expect_pc0);

            let mut s = s0;
            // TODO: avoid passing in the `live` flag, which is unused in bbmd
            s.live = b.lit(true);
            let mut mem_ports_iter = mem_ports.repr.into_iter();
            let mut advise_values_iter = advise_values.repr.into_iter();

            for (step_idx, pc) in self.block.iter_pcs().enumerate() {
                let instr = self.instrs[pc];
                let mut instr_counts = AdviceCounts::default();
                count_opcode_advice_inputs(instr.opcode(), &mut instr_counts);

                let instr_wire = b.lit(instr);

                let mem_port = if instr_counts.mem_ports == 0 {
                    b.lit(MemPort::default())
                } else {
                    mem_ports_iter.next().unwrap()
                };

                let advise_value = if instr_counts.advise == 0 {
                    b.lit(0)
                } else {
                    advise_values_iter.next().unwrap()
                };

                let (new_s, ci) = trace::calc_step_inner(
                    &cx,
                    b,
                    &mut ev,
                    &[],    // calc_step_inner_cases - unused
                    self.privilege_levels,
                    block_idx,
                    Some(instr.opcode()),
                    instr_wire,
                    &mem_port,
                    advise_value,
                    &s,
                    None,
                );

                trace::check_step_inner(
                    &cx,
                    b,
                    block_idx,
                    step_idx,
                    s.cycle,
                    s.live,
                    instr_wire,
                    mem_port,
                    &ci,
                );

                s = new_s;
            }

            let (asserts, bugs) = cx.finish(c);
            let result = (
                s,
                TWire::new(c.all_true(asserts.iter().map(|tw| tw.repr))),
                TWire::new(c.any_true(bugs.iter().map(|tw| tw.repr))),
            );
            let (result_wires, _result_sizes) =
                typed::to_wire_list(&TWire::<BlockFnResult>::new(result));

            c.pack(&result_wires)
        }
    }

    let c = b.circuit();
    let sizes = [params.num_regs, counts.mem_ports, counts.advise];
    let num_args = BlockFnArgs::expected_num_wires(&mut sizes.iter().copied());
    let mut arg_tys = Vec::with_capacity(num_args);
    BlockFnArgs::for_each_expected_wire_type(c, &mut sizes.iter().copied(), |t| arg_tys.push(t));
    let name = format!("block_{}", block_idx);
    c.define_function::<(), _>(&name, &arg_tys, BlockFunction {
        instrs,
        counts,
        block,
        block_idx,
        num_regs: params.num_regs,
        privilege_levels: params.privilege_levels,
    })
}

/// Define a function with the same signature as in `define_block_function`, but which passes
/// through the state unchanged.
fn define_no_op_block_function<'a>(
    b: &impl Builder<'a>,
    counts: &AdviceCounts,
    params: &Params,
) -> Function<'a> {
    struct NoOpFunction<'b> {
        counts: &'b AdviceCounts,
        num_regs: usize,
    }

    impl<'a, 'b> DefineFunction<'a> for NoOpFunction<'b> {
        fn build_body<C>(self, c: &C, args_wires: &[Wire<'a>]) -> Wire<'a>
        where C: CircuitTrait<'a> {
            let sizes = [self.num_regs, self.counts.mem_ports, self.counts.advise];
            let args = typed::from_wire_list::<BlockFnArgs>(c.as_base(), &args_wires, &sizes);
            let (s0, mem_ports, advise_values) = args.repr;

            let cx = Context::new(c);
            let b = BuilderImpl::from_ref(c);

            let (asserts, bugs) = cx.finish(c);
            let result = (
                // State is unchanged.
                s0,
                // All asserts passed.
                b.lit(true),
                // No bugs detected.
                b.lit(false),
            );
            let (result_wires, _result_sizes) =
                typed::to_wire_list(&TWire::<BlockFnResult>::new(result));

            c.pack(&result_wires)
        }
    }

    let c = b.circuit();
    let sizes = [params.num_regs, counts.mem_ports, counts.advise];
    let num_args = BlockFnArgs::expected_num_wires(&mut sizes.iter().copied());
    let mut arg_tys = Vec::with_capacity(num_args);
    BlockFnArgs::for_each_expected_wire_type(c, &mut sizes.iter().copied(), |t| arg_tys.push(t));
    c.define_function::<(), _>("block_no_op", &arg_tys, NoOpFunction {
        counts,
        num_regs: params.num_regs,
    })
}

