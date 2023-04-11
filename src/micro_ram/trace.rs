use std::collections::HashMap;
use std::iter;
use zk_circuit_builder::gadget::arith::BuilderExt as _;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::circuit::CircuitTrait;
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::typed::{TWire, Builder, BuilderExt, EvaluatorExt};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::{self, Fetch};
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::mem::{self, Memory, extract_bytes_at_offset, extract_low_bytes};
use crate::micro_ram::types::{
    self, CalcIntermediate, RamState, RamStateRepr, RamInstr, MemPort, Opcode, MemOpKind,
    MemOpWidth, Advice, REG_NONE, REG_PC, MEM_PORT_UNUSED_CYCLE
};
use crate::micro_ram::witness::{MultiExecWitness, SegmentWitness};
use crate::mode::if_mode::{AnyTainted, is_mode};
use crate::mode::tainted;



#[derive(Migrate)]
pub struct Segment<'a> {
    pub idx: usize,
    len: usize,
    states: Vec<TWire<'a, RamState>>,
    final_state: TWire<'a, RamState>,

    fetch_ports: Option<fetch::CyclePorts<'a>>,
    mem_ports: mem::CyclePorts<'a>,
}

pub struct SegmentBuilder<'a, 'b, B> {
    pub cx: &'b Context<'a>,
    pub b: &'b B,
    pub ev: &'b mut CachingEvaluator<'a, 'static, eval::Public>,
    pub mem: &'b mut Memory<'a>,
    pub fetch: &'b mut Fetch<'a>,
    pub params: &'b types::Params,
    pub prog: &'b [RamInstr],
    pub check_steps: usize,
}

impl<'a, 'b, B: Builder<'a>> SegmentBuilder<'a, 'b, B> {
    pub fn run(
        &mut self,
        idx: usize,
        s: &types::Segment,
        init_state: TWire<'a, RamState>,
        mut kmem: KnownMem<'a>,
        project_witness: impl Fn(&MultiExecWitness) -> &SegmentWitness + Copy + 'static,
    ) -> (Segment<'a>, KnownMem<'a>) {
        let cx = self.cx;
        let b = self.b;
        let ev = &mut self.ev;
        let _g = b.scoped_label(format_args!("trace/{}", s.desc()));

        let mut mem_ports: mem::CyclePorts;
        let fetch_ports: Option<fetch::CyclePorts>;
        if let Some(init_pc) = s.init_pc() {
            let prog = self.prog;
            mem_ports = self.mem.add_cycles_irregular(
                cx, b,
                s.len,
                (0 .. s.len).filter(|i| prog[init_pc as usize + i].opcode().is_mem()),
                project_witness,
            );
            fetch_ports = None;
        } else {
            mem_ports = self.mem.add_cycles(
                cx, b,
                s.len,
                self.params.sparsity.mem_op,
                project_witness,
            );
            fetch_ports = Some(self.fetch.add_cycles(b, s.len, project_witness));
        };

        let mut states = Vec::new();

        if let Some(init_pc) = s.init_pc() {
            let init_state_pc = init_state.pc;
            cx.when(b, init_state.live, |cx| {
                wire_assert!(
                    cx, b, b.eq(init_state_pc, b.lit(init_pc)),
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
                let instr_val = self.prog[pc as usize];
                instr = b.lit(instr_val);
            } else {
                let fp = fetch_ports.as_ref().unwrap().get(i);
                {
                    // Check that the fetch port is consistent with the step taken.
                    let addr = fp.addr;
                    let pc = prev_state.pc;
                    cx.when(b, prev_state.live, |cx| {
                        wire_assert!(
                            cx, b, b.eq(addr, pc),
                            "segment {}: fetch in slot {} accesses address {:x} (expected {:x})",
                            idx, i, cx.eval(addr), cx.eval(pc),
                        );
                    });
                }
                instr = fp.instr;

                // Stutter advice only makes sense in secret segments.
                let stutter = b.secret_lazy(move |w: &MultiExecWitness| {
                    let w = project_witness(w);
                    w.stutter[i]
                });
                instr.opcode = b.mux(stutter, b.lit(Opcode::Stutter as u8), instr.opcode);
                instr.opcode = b.mux(prev_state.live, instr.opcode, b.lit(Opcode::Stutter as u8));
            };
            let instr = instr;

            let mem_port = mem_ports.get(b, i);
            let advice = b.secret_lazy(move |w: &MultiExecWitness| {
                let w = project_witness(w);
                w.advice[i]
            });

            let (calc_state, calc_im) =
                calc_step(cx, b, ev, i, instr, &mem_port, advice, &prev_state, &mut kmem);
            if calc_im.mem_port_unused {
                mem_ports.set_unused(i);
            }
            check_step(cx, b, idx, i,
                prev_state.cycle, prev_state.live, instr, mem_port, &calc_im);
            if self.check_steps > 0 {
                states.push(calc_state.clone());
            }
            prev_state = calc_state;
        }

        let seg = Segment {
            idx,
            len: s.len,
            states,
            final_state: prev_state,
            fetch_ports,
            mem_ports,
        };
        (seg, kmem)
    }
}

impl<'a> Segment<'a> {
    pub fn final_state(&self) -> &TWire<'a, RamState> {
        &self.final_state
    }

    pub fn check_states(
        &self,
        cx: &Context<'a>,
        b: &impl Builder<'a>,
        init_cycle: u32,
        check_steps: usize,
        states: &[RamState],
    ) {
        let _g = b.scoped_label("trace");
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
        b: &impl Builder<'a>,
        cycle: u32,
        actual: &TWire<'a, RamState>,
        expected: &RamState,
    ) {
        check_state(cx, b, self.idx, cycle, actual, &b.lit(expected.clone()));
    }
}


fn operand_value<'a>(
    b: &impl Builder<'a>,
    s: &TWire<'a, RamState>,
    op: TWire<'a, u64>,
    imm: TWire<'a, bool>,
) -> TWire<'a, u64> {
    let reg_val = b.index(&s.regs, op, |b, i| b.lit(i as u64));
    b.mux(imm, op, reg_val)
}

fn calc_step<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    ev: &mut CachingEvaluator<'a, '_, eval::Public>,
    idx: usize,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    advice: TWire<'a, u64>,
    s1: &TWire<'a, RamState>,
    kmem: &mut KnownMem<'a>,
) -> (TWire<'a, RamState>, CalcIntermediate<'a>) {
    let _g = b.scoped_label("calc_step");

    let opcode = ev.eval_typed(b.circuit(), instr.opcode).and_then(Opcode::from_raw);

    let mut cases = Vec::new();
    // This has to be defined outside the macro so it's visible to the body expressions passed to
    // `case!` below.
    let mut dest: TWire<u8>;
    macro_rules! case {
        ($op:expr, $body:expr) => {
            if opcode.is_none() || opcode == Some($op) {
                // This write is dead in some cases.
                #[allow(unused)] {
                    dest = instr.dest;
                }
                let result: TWire<u64> = $body;
                let op_match = if opcode.is_none() {
                    b.eq(b.lit($op as u8), instr.opcode)
                } else {
                    b.lit(true)
                };
                let parts = TWire::<(_, _)>::new((result, dest));
                cases.push(TWire::<(_, _)>::new((op_match, parts)));
            }
        };
    }

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u8));
    let y = operand_value(b, s1, instr.op2, instr.imm);

    // This flag is set if the `MemPort` is publicly known to be unused.  `Load*` ops may set this
    // if `opcode` is known; otherwise, all non-memory ops set this below.
    let mut mem_port_unused = false;


    case!(Opcode::And, b.and(x, y));
    case!(Opcode::Or, b.or(x, y));
    case!(Opcode::Xor, b.xor(x, y));
    case!(Opcode::Not, b.not(y));

    case!(Opcode::Add, b.add(x, y));
    case!(Opcode::Sub, b.sub(x, y));
    case!(Opcode::Mull, b.mul(x, y));
    case!(Opcode::Umulh, {
        let (_, high) = *b.wide_mul(x, y);
        high
    });
    case!(Opcode::Smulh, {
        let (_, high_s) = *b.wide_mul(b.cast::<_, i64>(x), b.cast::<_, i64>(y));
        // TODO: not sure this gives the right overflow value - what if high = -1?
        b.cast::<_, u64>(high_s)
    });
    case!(Opcode::Udiv, b.div(x, y));
    case!(Opcode::Umod, b.mod_(x, y));

    case!(Opcode::Shl, b.shl(x, b.cast(y)));
    case!(Opcode::Shr, b.shr(x, b.cast(y)));

    case!(Opcode::Cmpe, b.cast(b.eq(x, y)));
    case!(Opcode::Cmpa, b.cast(b.gt(x, y)));
    case!(Opcode::Cmpae, b.cast(b.ge(x, y)));
    case!(Opcode::Cmpg, b.cast(b.gt(b.cast::<_, i64>(x), b.cast::<_, i64>(y))));
    case!(Opcode::Cmpge, b.cast(b.ge(b.cast::<_, i64>(x), b.cast::<_, i64>(y))));

    case!(Opcode::Mov, y);
    case!(Opcode::Cmov, {
        dest = b.mux(b.neq_zero(x), instr.dest, b.lit(REG_NONE));
        y
    });

    case!(Opcode::Jmp, {
        dest = b.lit(REG_PC);
        y
    });
    // TODO: Double check. Is this `x`?
    // https://gitlab-ext.galois.com/fromager/cheesecloth/MicroRAM/-/merge_requests/33/diffs#d54c6573feb6cf3e6c98b0191e834c760b02d5c2_94_71
    case!(Opcode::Cjmp, {
        dest = b.mux(b.neq_zero(x), b.lit(REG_PC), b.lit(REG_NONE));
        y
    });
    case!(Opcode::Cnjmp, {
        dest = b.mux(b.neq_zero(x), b.lit(REG_NONE), b.lit(REG_PC));
        y
    });

    // Load1, Load2, Load4, Load8
    for w in MemOpWidth::iter() {
        case!(w.load_opcode(), {
            let addr = y;
            let known_value = if opcode == Some(w.load_opcode()) {
                kmem.load(b, ev, addr, w)
            } else {
                None
            };
            if let Some(known_value) = known_value {
                mem_port_unused = true;
                known_value
            } else {
                extract_bytes_at_offset(b, mem_port.value, mem_port.addr, w)
            }
        });
    }
    // Store1, Store2, Store4, Store8
    for w in MemOpWidth::iter() {
        case!(w.store_opcode(), {
            dest = b.lit(REG_NONE);
            if opcode == Some(w.store_opcode()) {
                let (addr, value) = (y, x);
                kmem.store(b, ev, addr, value, w);
            }
            b.lit(0)
        });
    }
    case!(Opcode::Poison8, {
        dest = b.lit(REG_NONE);
        if opcode == Some(Opcode::Poison8) {
            let (addr, value) = (y, x);
            kmem.poison(b, ev, addr, value, MemOpWidth::W8);
        }
        b.lit(0)
    });

    // TODO: dummy implementation of `Answer` as a no-op infinite loop
    case!(Opcode::Answer, {
        dest = b.lit(REG_PC);
        s1.pc
    });

    case!(Opcode::Advise, {
        if opcode == Some(Opcode::Advise) {
            if let Some(max) = ev.eval_typed(b.circuit(), y) {
                wire_assert!(
                    cx, b, b.le(advice, b.lit(max)),
                    "step {}: advice value {} is out of range (expected <= {})",
                    idx, cx.eval(advice), max,
                );
                kmem.set_wire_range(advice, max);
            }
        }
        advice
    });

    // A no-op that doesn't advance the `pc`.  Specifically, this works by jumping to the
    // current `pc`.
    case!(Opcode::Stutter, {
        dest = b.lit(REG_PC);
        s1.pc
    });


    if is_mode::<AnyTainted>() {
        // Opcode::Sink is a no-op in the standard interpreter.
        case!(Opcode::Sink1, {
            dest = b.lit(REG_NONE);
            b.lit(0)
        });

        // Opcode::Taint is a no-op in the standard intepreter, but we need to set the dest for the
        // later taint handling step. We set the value back to itself so that taint operations are treated
        // like `mov rX rX`.
        case!(Opcode::Taint1, {
            dest = instr.op1;
            x
        });
    }

    let (result, dest) = if opcode.is_some() {
        if cases.len() == 1 {
            *cases[0].1
        } else {
            b.lit((0, REG_NONE)).repr
        }
    } else {
        *b.mux_multi(&cases, b.lit((0, REG_NONE)))
    };

    let mut regs = TWire::<Vec<_>>::new(Vec::with_capacity(s1.regs.len()));
    for (i, &v_old) in s1.regs.iter().enumerate() {
        let is_dest = b.eq(b.lit(i as u8), dest);
        regs.push(b.mux(is_dest, result, v_old));
    }

    let (tainted_regs, tainted_im) = tainted::calc_step(
        cx, b, idx, instr, mem_port, &s1.tainted_regs, x, y, dest);

    let pc_is_dest = b.eq(b.lit(REG_PC), dest);
    let pc = b.mux(pc_is_dest, result, b.add(s1.pc, b.lit(1)));

    let cycle = b.add(s1.cycle, b.lit(1));
    let live = s1.live;

    if let Some(opcode) = opcode {
        if !opcode.is_mem() {
            mem_port_unused = true;
        }
    } else {
        // The opcode is unknown, so it could be performing any store at any address.
        kmem.clear();
    }

    let s2 = RamStateRepr { cycle, pc, regs, live, tainted_regs };
    let im = CalcIntermediate {
        x, y, result,
        tainted: tainted_im,
        mem_port_unused,
    };
    (TWire::new(s2), im)
}

fn check_state<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    seg_idx: usize,
    cycle: u32,
    calc_s: &TWire<'a, RamState>,
    trace_s: &TWire<'a, RamState>,
) {
    let _g = b.scoped_label("check_state");

    for (i, (&v_calc, &v_new)) in calc_s.regs.iter().zip(trace_s.regs.iter()).enumerate() {
        wire_assert!(
            cx, b, b.eq(v_new, v_calc),
            "segment {}: cycle {} sets reg {} to {} (expected {})",
            seg_idx, cycle, i, cx.eval(v_new), cx.eval(v_calc),
        );
    }

    let trace_pc = trace_s.pc;
    let calc_pc = calc_s.pc;
    wire_assert!(
        cx, b, b.eq(trace_pc, calc_pc),
        "segment {}: cycle {} sets pc to {} (expected {})",
        seg_idx, cycle, cx.eval(trace_pc), cx.eval(calc_pc),
    );

    // Cycle `N` increments the cycle counter by 1 and ends with `calc_s.cycle == N + 1`.
    let trace_cycle = b.lit(cycle + 1);
    let calc_cycle = calc_s.cycle;
    wire_assert!(
        cx, b, b.eq(trace_cycle, calc_cycle),
        "segment {}: cycle {} sets cycle to {} (expected {})",
        seg_idx, cycle, cx.eval(trace_cycle), cx.eval(calc_cycle),
    );

    tainted::check_state(cx, b, cycle, &calc_s.tainted_regs, &trace_s.tainted_regs);
}

fn check_step<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    seg_idx: usize,
    idx: usize,
    cycle: TWire<'a, u32>,
    live: TWire<'a, bool>,
    instr: TWire<'a, RamInstr>,
    mem_port: TWire<'a, MemPort>,
    calc_im: &CalcIntermediate<'a>,
) {
    let _g = b.scoped_label("check_step");

    let x = calc_im.x;
    let y = calc_im.y;

    if !calc_im.mem_port_unused {
        // If the instruction is a store, load, or poison, we need additional checks to make sure
        // the fields of `mem_port` match the instruction operands.
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
        // segments).  for secret segments we can continue to rely on non-live segments running
        // nothing but `Opcode::Stutter`.

        cx.when(b, b.and(is_mem, live), |cx| {
            wire_assert!(
                cx, b, b.eq(mem_port.addr, addr),
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
                        cx, b, b.eq(mem_port.op, b.lit(op)),
                        "segment {}: step {}'s mem port has op kind {} (expected {}, {:?})",
                        seg_idx, idx, cx.eval(mem_port.op.repr), op as u8, op,
                    );
                });
            }
            tainted::check_step_mem(
                cx, b, seg_idx, idx, &mem_port, &is_store_like, &calc_im.tainted);
        });

        for w in MemOpWidth::iter() {
            cx.when(b, b.and(b.eq(instr.opcode, b.lit(w.store_opcode() as u8)), live), |cx| {
                wire_assert!(
                    cx, b, b.eq(mem_port.width, b.lit(w)),
                    "segment {}: step {}'s mem port has width {:?} (expected {:?})",
                    seg_idx, idx, cx.eval(mem_port.width), w,
                );

                let stored_value = extract_bytes_at_offset(b, mem_port.value, mem_port.addr, w);
                let x_low = extract_low_bytes(b, x, w);
                wire_assert!(
                    cx, b, b.eq(stored_value, x_low),
                    "segment {}: step {}'s mem port stores value {} at {:x} (expected value {})",
                    seg_idx, idx, cx.eval(stored_value), cx.eval(mem_port.addr), cx.eval(x),
                );
            });
        }

        cx.when(b, b.and(is_poison, live), |cx| {
            wire_assert!(
                cx, b, b.eq(mem_port.width, b.lit(MemOpWidth::W8)),
                "segment {}: step {}'s mem port has width {:?} (expected {:?})",
                seg_idx, idx, cx.eval(mem_port.width), MemOpWidth::W8,
            );
        });

        // Either `mem_port.cycle == cycle` and this step is a mem op, or `mem_port.cycle ==
        // MEM_PORT_UNUSED_CYCLE` and this is not a mem op.  Other `mem_port.cycle` values are
        // invalid.
        let expect_cycle = b.mux(b.and(is_mem, live), cycle, b.lit(MEM_PORT_UNUSED_CYCLE));
        wire_assert!(
            cx, b, b.eq(mem_port.cycle, expect_cycle),
            "segment {}: step {} mem port cycle number is {} (expected {}; mem op? {})",
            seg_idx, idx, cx.eval(mem_port.cycle), cx.eval(expect_cycle), cx.eval(is_mem),
        );
    }

    tainted::check_step(cx, b, seg_idx, idx, instr, calc_im);
}
