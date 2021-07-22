use std::collections::HashMap;
use std::iter;
use crate::gadget::arith::BuilderExt as _;
use crate::ir::typed::{TWire, TSecretHandle, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::{self, Fetch};
use crate::micro_ram::mem::{self, Memory, extract_bytes_at_offset, extract_low_bytes};
use crate::micro_ram::types::{
    self, CalcIntermediate, RamState, RamStateRepr, RamInstr, MemPort, Opcode, MemOpKind, MemOpWidth, Advice,
    REG_NONE, REG_PC, MEM_PORT_UNUSED_CYCLE
};
use crate::mode::tainted;



pub struct Segment<'a> {
    pub idx: usize,
    len: usize,
    states: Vec<TWire<'a, RamState>>,
    final_state: TWire<'a, RamState>,

    fetch_ports: Option<fetch::CyclePorts<'a>>,
    mem_ports: mem::CyclePorts<'a>,
    advice_secrets: Vec<TSecretHandle<'a, u64>>,
    stutter_secrets: Vec<TSecretHandle<'a, bool>>,

}

pub struct SegmentBuilder<'a, 'b> {
    pub cx: &'b Context<'a>,
    pub b: &'b Builder<'a>,
    pub mem: &'b mut Memory<'a>,
    pub fetch: &'b mut Fetch<'a>,
    pub params: &'b types::Params,
    pub prog: &'b [RamInstr],
    pub check_steps: usize,
}

impl<'a, 'b> SegmentBuilder<'a, 'b> {
    pub fn run(
        &mut self,
        idx: usize,
        s: &types::Segment,
        init_state: TWire<'a, RamState>,
    ) -> Segment<'a> {
        let cx = self.cx;
        let b = self.b;

        let mem_ports: mem::CyclePorts;
        let fetch_ports: Option<fetch::CyclePorts>;
        if let Some(init_pc) = s.init_pc() {
            let prog = self.prog;
            mem_ports = self.mem.add_cycles_irregular(
                cx, b,
                s.len,
                (0 .. s.len).filter(|i| prog[init_pc as usize + i].opcode().is_mem()),
            );
            fetch_ports = None;
        } else {
            mem_ports = self.mem.add_cycles(
                cx, b,
                s.len,
                self.params.sparsity.mem_op,
            );
            fetch_ports = Some(self.fetch.add_cycles(b, s.len));
        };
        let advice_secrets: Vec<TSecretHandle<u64>> =
            iter::repeat_with(|| b.secret().1).take(s.len).collect();
        let stutter_secrets: Vec<TSecretHandle<bool>> =
            iter::repeat_with(|| b.secret().1).take(s.len).collect();

        let mut states = Vec::new();

        if let Some(init_pc) = s.init_pc() {
            let init_state_pc = init_state.pc;
            cx.when(b, init_state.live, |cx| {
                wire_assert!(
                    cx, b.eq(init_state_pc, b.lit(init_pc)),
                    "segment {}: initial pc is {:x} (expected {:x})",
                    idx, cx.eval(init_state_pc), init_pc,
                );
            });
            // TODO: assert that there are no jmps within the segment except at the end (regular
            // assert!, since this can be checked with only public info)
        }

        let mut prev_state = init_state.clone();
        for i in 0 .. s.len {
            // Get the instruction to execute.
            let mut instr;
            if let Some(init_pc) = s.init_pc() {
                let pc = init_pc + i as u64;
                instr = b.lit(self.prog[pc as usize]);
            } else {
                let fp = fetch_ports.as_ref().unwrap().get(i);
                {
                    // Check that the fetch port is consistent with the step taken.
                    let addr = fp.addr;
                    let pc = prev_state.pc;
                    wire_assert!(
                        cx, b.eq(addr, pc),
                        "segment {}: fetch in slot {} accesses address {:x} (expected {:x})",
                        idx, i, cx.eval(addr), cx.eval(pc),
                    );
                }
                instr = fp.instr;

                // Stutter advice only makes sense in secret segments.
                let stutter = stutter_secrets[i].wire().clone();
                instr.opcode = b.mux(stutter, b.lit(Opcode::Stutter as u8), instr.opcode);
                instr.opcode = b.mux(prev_state.live, instr.opcode, b.lit(Opcode::Stutter as u8));
            };
            let instr = instr;

            let mem_port = mem_ports.get(b, i);
            let advice = advice_secrets[i].wire().clone();

            let (calc_state, calc_im) =
                calc_step(&cx, &b, i, instr, &mem_port, advice, &prev_state);
            check_step(&cx, &b, idx, i,
                prev_state.cycle, prev_state.live, instr, mem_port, &calc_im);
            if self.check_steps > 0 {
                states.push(calc_state.clone());
            }
            prev_state = calc_state;
        }

        Segment {
            idx,
            len: s.len,
            states,
            final_state: prev_state,
            fetch_ports,
            mem_ports,
            advice_secrets,
            stutter_secrets,
        }
    }
}

impl<'a> Segment<'a> {
    pub fn final_state(&self) -> &TWire<'a, RamState> {
        &self.final_state
    }

    pub fn set_states(
        &mut self,
        b: &Builder<'a>,
        prog: &[RamInstr],
        init_cycle: u32,
        init_state: &RamState,
        states: &[RamState],
        advice: &HashMap<u64, Vec<Advice>>,
    ) {
        assert_eq!(states.len(), self.len);
        let states_iter = iter::once(init_state).chain(states.iter()).take(self.len);
        for (i, state) in states_iter.enumerate() {
            let cycle = init_cycle + i as u32;

            if let Some(ref mut fetch_ports) = self.fetch_ports {
                let pc = state.pc;
                let instr = prog.get(pc as usize).cloned().unwrap_or_else(|| panic!(
                    "program executed out of bounds (pc = 0x{:x}) on cycle {}", pc, cycle,
                ));
                fetch_ports.set(b, i, pc, instr);
            }

            let k = cycle as u64 + 1;
            let adv_list = advice.get(&k).map_or(&[] as &[_], |v| v as &[_]);
            for adv in adv_list {
                match *adv {
                    Advice::MemOp { addr, value, op, width, tainted } => {
                        self.mem_ports.set_port(b, i, MemPort { cycle, addr, value, op, width, tainted });
                    },
                    Advice::Stutter => {
                        self.stutter_secrets[i].set(b, true);
                    },
                    Advice::Advise { advise } => {
                        self.advice_secrets[i].set(b, advise);
                    },
                }
            }
        }
    }

    pub fn check_states(
        &self,
        cx: &Context<'a>,
        b: &Builder<'a>,
        init_cycle: u32,
        check_steps: usize,
        states: &[RamState],
    ) {
        assert_eq!(states.len(), self.len);
        let mut did_final = false;
        if check_steps > 0 {
            for i in (0 .. self.len).step_by(check_steps) {
                let cycle = init_cycle + i as u32;
                let actual = &self.states[i];
                self.check_state(cx, b, cycle, actual, &states[i]);
                if i == self.len - 1 {
                    did_final = true;
                }
            }
        }
        if !did_final && self.len > 0 {
            let cycle = init_cycle + self.len as u32 - 1;
            let actual = &self.final_state;
            self.check_state(cx, b, cycle, actual, states.last().unwrap());
        }
    }

    fn check_state(
        &self,
        cx: &Context<'a>,
        b: &Builder<'a>,
        cycle: u32,
        actual: &TWire<'a, RamState>,
        expected: &RamState,
    ) {
        check_state(cx, b, self.idx, cycle, actual, &b.lit(expected.clone()));
    }
}


fn operand_value<'a>(
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
    op: TWire<'a, u64>,
    imm: TWire<'a, bool>,
) -> TWire<'a, u64> {
    let reg_val = b.index(&s.regs, op, |b, i| b.lit(i as u64));
    b.mux(imm, op, reg_val)
}

fn calc_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    idx: usize,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    advice: TWire<'a, u64>,
    s1: &TWire<'a, RamState>,
) -> (TWire<'a, RamState>, CalcIntermediate<'a>) {
    let _g = b.scoped_label(format_args!("calc_step/cycle {}", idx));

    // TODO: Where do we get instr from? PC wire of s1? Or still advice?

    let mut cases = Vec::new();
    let mut add_case = |op, result, dest| {
        let op_match = b.eq(b.lit(op as u8), instr.opcode);
        let parts = TWire::<(_, _)>::new((result, dest));
        cases.push(TWire::<(_, _)>::new((op_match, parts)));
    };

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u8));
    let y = operand_value(b, s1, instr.op2, instr.imm);

    {
        let result = b.and(x, y);
        add_case(Opcode::And, result, instr.dest);
    }

    {
        let result = b.or(x, y);
        add_case(Opcode::Or, result, instr.dest);
    }

    {
        let result = b.xor(x, y);
        add_case(Opcode::Xor, result, instr.dest);
    }

    {
        let result = b.not(y);
        add_case(Opcode::Not, result, instr.dest);
    }

    {
        add_case(Opcode::Add, b.add(x, y), instr.dest);
    }

    {
        add_case(Opcode::Sub, b.sub(x, y), instr.dest);
    }

    {
        add_case(Opcode::Mull, b.mul(x, y), instr.dest);
    }

    {
        let (_, high) = *b.wide_mul(x, y);
        add_case(Opcode::Umulh, high, instr.dest);
    }

    {
        let (_, high_s) = *b.wide_mul(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        // TODO: not sure this gives the right overflow value - what if high = -1?
        add_case(Opcode::Smulh, b.cast::<_, u64>(high_s), instr.dest);
    }

    {
        let result = b.div(x, y);
        add_case(Opcode::Udiv, result, instr.dest);
    }

    {
        let result = b.mod_(x, y);
        add_case(Opcode::Umod, result, instr.dest);
    }

    {
        let result = b.shl(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shl, result, instr.dest);
    }

    {
        let result = b.shr(x, b.cast::<_, u8>(y));
        add_case(Opcode::Shr, result, instr.dest);
    }


    {
        let result = b.cast::<_, u64>(b.eq(x, y));
        add_case(Opcode::Cmpe, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.gt(x, y));
        add_case(Opcode::Cmpa, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.ge(x, y));
        add_case(Opcode::Cmpae, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.gt(b.cast::<_, i64>(x), b.cast::<_, i64>(y)));
        add_case(Opcode::Cmpg, result, instr.dest);
    }

    {
        let result = b.cast::<_, u64>(b.ge(b.cast::<_, i64>(x), b.cast::<_, i64>(y)));
        add_case(Opcode::Cmpge, result, instr.dest);
    }


    {
        add_case(Opcode::Mov, y, instr.dest);
    }

    {
        let dest = b.mux(b.neq_zero(x), instr.dest, b.lit(REG_NONE));
        add_case(Opcode::Cmov, y, dest);
    }


    {
        add_case(Opcode::Jmp, y, b.lit(REG_PC));
    }

    // TODO: Double check. Is this `x`?
    // https://gitlab-ext.galois.com/fromager/cheesecloth/MicroRAM/-/merge_requests/33/diffs#d54c6573feb6cf3e6c98b0191e834c760b02d5c2_94_71
    {
        let dest = b.mux(b.neq_zero(x), b.lit(REG_PC), b.lit(REG_NONE));
        add_case(Opcode::Cjmp, y, dest);
    }

    {
        let dest = b.mux(b.neq_zero(x), b.lit(REG_NONE), b.lit(REG_PC));
        add_case(Opcode::Cnjmp, y, dest);
    }

    // Load1, Load2, Load4, Load8
    for w in MemOpWidth::iter() {
        let result = extract_bytes_at_offset(b, mem_port.value, mem_port.addr, w);
        add_case(w.load_opcode(), result, instr.dest);
    }

    // Store1, Store2, Store4, Store8
    for w in MemOpWidth::iter() {
        add_case(w.store_opcode(), b.lit(0), b.lit(REG_NONE));
    }

    {
        add_case(Opcode::Poison8, b.lit(0), b.lit(REG_NONE));
    }

    {
        // TODO: dummy implementation of `Answer` as a no-op infinite loop
        add_case(Opcode::Answer, s1.pc, b.lit(REG_PC));
    }

    {
        add_case(Opcode::Advise, advice, instr.dest);
    }

    {
        // A no-op that doesn't advance the `pc`.  Specifically, this works by jumping to the
        // current `pc`.
        add_case(Opcode::Stutter, s1.pc, b.lit(REG_PC));
    }

    // Opcode::Sink is a no-op in the standard interpreter, so we let if fall through to the default below.
    // Opcode::Taint is a no-op in the standard intepreter, but we need to set the dest for the
    // later taint handling step. We set the value back to itself so that taint operations are treated
    // like `mov rX rX`.
    {
        add_case(Opcode::Taint, x, instr.op1);
    }

    let (result, dest) = *b.mux_multi(&cases, b.lit((0, REG_NONE)));

    let mut regs = Vec::with_capacity(s1.regs.len());
    for (i, &v_old) in s1.regs.iter().enumerate() {
        let is_dest = b.eq(b.lit(i as u8), dest);
        regs.push(b.mux(is_dest, result, v_old));
    }

    let (tainted_regs, tainted_im) = tainted::calc_step(cx, b, idx, instr, mem_port, &s1.tainted_regs, y, dest);

    let pc_is_dest = b.eq(b.lit(REG_PC), dest);
    let pc = b.mux(pc_is_dest, result, b.add(s1.pc, b.lit(1)));

    let cycle = b.add(s1.cycle, b.lit(1));
    let live = s1.live;

    let s2 = RamStateRepr { cycle, pc, regs, live, tainted_regs };
    let im = CalcIntermediate { x, y, result, tainted: tainted_im };
    (TWire::new(s2),im)
}

fn check_state<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    seg_idx: usize,
    cycle: u32,
    calc_s: &TWire<'a, RamState>,
    trace_s: &TWire<'a, RamState>,
) {
    let _g = b.scoped_label(format_args!("check_state/{}", cycle));

    for (i, (&v_calc, &v_new)) in calc_s.regs.iter().zip(trace_s.regs.iter()).enumerate() {
        wire_assert!(
            cx, b.eq(v_new, v_calc),
            "segment {}: cycle {} sets reg {} to {} (expected {})",
            seg_idx, cycle, i, cx.eval(v_new), cx.eval(v_calc),
        );
    }

    let trace_pc = trace_s.pc;
    let calc_pc = calc_s.pc;
    wire_assert!(
        cx, b.eq(trace_pc, calc_pc),
        "segment {}: cycle {} sets pc to {} (expected {})",
        seg_idx, cycle, cx.eval(trace_pc), cx.eval(calc_pc),
    );

    // Cycle `N` increments the cycle counter by 1 and ends with `calc_s.cycle == N + 1`.
    let trace_cycle = b.lit(cycle + 1);
    let calc_cycle = calc_s.cycle;
    wire_assert!(
        cx, b.eq(trace_cycle, calc_cycle),
        "segment {}: cycle {} sets cycle to {} (expected {})",
        seg_idx, cycle, cx.eval(trace_cycle), cx.eval(calc_cycle),
    );

    tainted::check_state(cx, b, cycle, &calc_s.tainted_regs, &trace_s.tainted_regs);
}

fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    seg_idx: usize,
    idx: usize,
    cycle: TWire<'a, u32>,
    live: TWire<'a, bool>,
    instr: TWire<'a, RamInstr>,
    mem_port: TWire<'a, MemPort>,
    calc_im: &CalcIntermediate<'a>,
) {
    let _g = b.scoped_label(format_args!("check_step/{},{}", seg_idx, idx));

    let x = calc_im.x;
    let y = calc_im.y;

    // If the instruction is a store, load, or poison, we need additional checks to make sure the
    // fields of `mem_port` match the instruction operands.
    let is_load = MemOpWidth::iter().map(|w| w.load_opcode())
        .fold(b.lit(false), |acc, op| b.or(acc, b.eq(instr.opcode, b.lit(op as u8))));
    let is_store = MemOpWidth::iter().map(|w| w.store_opcode())
        .fold(b.lit(false), |acc, op| b.or(acc, b.eq(instr.opcode, b.lit(op as u8))));
    let is_poison = b.eq(instr.opcode, b.lit(Opcode::Poison8 as u8));
    let is_store_like = b.or(is_store, is_poison);
    let is_mem = b.or(is_load, is_store_like);

    let addr = y;

    // TODO: we could avoid most of the `live` checks if public-pc segments set appropriate
    // defaults when constructing their MemPorts (so the checks automatically pass on non-live
    // segments).  for secret segments we can continue to rely on non-live segments running nothing
    // but `Opcode::Stutter`.

    cx.when(b, b.and(is_mem, live), |cx| {
        wire_assert!(
            cx, b.eq(mem_port.addr, addr),
            "segment {}: step {}'s mem port has address {} (expected {})",
            seg_idx, idx, cx.eval(mem_port.addr), cx.eval(addr),
        );
        let flag_ops = [
            (is_load, MemOpKind::Read),
            (is_store, MemOpKind::Write),
            (is_poison, MemOpKind::Poison),
        ];
        for &(flag, op) in flag_ops.iter() {
            cx.when(b, flag, |cx| {
                wire_assert!(
                    cx, b.eq(mem_port.op, b.lit(op)),
                    "segment {}: step {}'s mem port has op kind {} (expected {}, {:?})",
                    seg_idx, idx, cx.eval(mem_port.op.repr), op as u8, op,
                );
            });
        }
        tainted::check_step_mem(cx, b, seg_idx, idx, &mem_port, &is_store_like, &calc_im.tainted);
    });

    for w in MemOpWidth::iter() {
        cx.when(b, b.and(b.eq(instr.opcode, b.lit(w.store_opcode() as u8)), live), |cx| {
            wire_assert!(
                cx, b.eq(mem_port.width, b.lit(w)),
                "segment {}: step {}'s mem port has width {:?} (expected {:?})",
                seg_idx, idx, cx.eval(mem_port.width), w,
            );

            let stored_value = extract_bytes_at_offset(b, mem_port.value, mem_port.addr, w);
            let x_low = extract_low_bytes(b, x, w);
            wire_assert!(
                cx, b.eq(stored_value, x_low),
                "segment {}: step {}'s mem port stores value {} at {:x} (expected value {})",
                seg_idx, idx, cx.eval(stored_value), cx.eval(mem_port.addr), cx.eval(x),
            );
        });
    }

    cx.when(b, b.and(is_poison, live), |cx| {
        wire_assert!(
            cx, b.eq(mem_port.width, b.lit(MemOpWidth::W8)),
            "segment {}: step {}'s mem port has width {:?} (expected {:?})",
            seg_idx, idx, cx.eval(mem_port.width), MemOpWidth::W8,
        );
    });

    // Either `mem_port.cycle == cycle` and this step is a mem op, or `mem_port.cycle ==
    // MEM_PORT_UNUSED_CYCLE` and this is not a mem op.  Other `mem_port.cycle` values are invalid.
    let expect_cycle = b.mux(b.and(is_mem, live), cycle, b.lit(MEM_PORT_UNUSED_CYCLE));
    wire_assert!(
        cx, b.eq(mem_port.cycle, expect_cycle),
        "segment {}: step {} mem port cycle number is {} (expected {}; mem op? {})",
        seg_idx, idx, cx.eval(mem_port.cycle), cx.eval(expect_cycle), cx.eval(is_mem),
    );

    tainted::check_step(cx, b, idx, instr, calc_im);
}
