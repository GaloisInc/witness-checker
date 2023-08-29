use std::collections::{HashMap, BTreeMap};
use std::convert::TryFrom;
use std::iter;
use std::ops::Index;
use zk_circuit_builder::gadget::arith::BuilderExt as _;
use zk_circuit_builder::eval::{self, CachingEvaluator};
use zk_circuit_builder::ir::circuit::{
    CircuitTrait, CircuitExt, CircuitBase, Circuit, CircuitFilter, Wire, Function, Bits, Ty, SwitchCase, DefineFunction,
};
use zk_circuit_builder::ir::migrate::{self, Migrate};
use zk_circuit_builder::ir::typed::{
    self, TWire, Builder, BuilderExt, BuilderImpl, EvaluatorExt, FromWireList, ToWireList,
};
use crate::micro_ram::context::Context;
use crate::micro_ram::fetch::{self, Fetch};
use crate::micro_ram::known_mem::KnownMem;
use crate::micro_ram::mem::{self, Memory, extract_bytes_at_offset, extract_low_bytes};
use crate::micro_ram::types::{
    self, CalcIntermediate, TaintCalcIntermediate, RamState, RamStateRepr, RamInstr, MemPort,
    Opcode, MemOpKind, MemOpWidth, Advice, CodeSegment, WordLabel, Label, ByteOffset, REG_NONE,
    REG_PC, MEM_PORT_UNUSED_CYCLE
};
use crate::micro_ram::witness::{MultiExecWitness, SegmentWitness};
use crate::mode::if_mode::{IfMode, AnyTainted, is_mode};
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
    pub privilege_levels: bool,
    pub calc_step_func: Function<'a>,
    pub calc_step_inner_cases: &'b [(Bits<'a>, Function<'a>)],
    pub check_step_func: Function<'a>,
    pub mem: &'b mut Memory<'a>,
    pub fetch: &'b mut Fetch<'a>,
    pub params: &'b types::Params,
    pub prog: &'b InstrLookup<'b>,
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
                (0 .. s.len).filter(|&i| prog[init_pc + i as u64].opcode().is_mem()),
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
                let instr_val = self.prog[pc];
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
                calc_step(cx, b, ev, self.privilege_levels, self.calc_step_func, self.calc_step_inner_cases,
                    i, instr, &mem_port, advice, &prev_state, &mut kmem);
            if calc_im.mem_port_unused {
                mem_ports.set_unused(i);
            }
            check_step(cx, b, self.check_step_func, idx, i,
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

type CalcIntermediateTypes = (
    u64, u64, u64,
    IfMode<AnyTainted, WordLabel>,
    IfMode<AnyTainted, Label>,
    IfMode<AnyTainted, WordLabel>,
    IfMode<AnyTainted, ByteOffset>,
    u64,
);

type CalcStepArgs = (RamInstr, MemPort, u64, RamState);

// `(x, y, pc, mem_port, advice, dest)` where `x` is the first operand, `y` is the second operand,
// `pc` is the program counter, `mem_port` is advice for memory operations, `advice` is advice from the
// `Advise` op, and `dest` is the destination index
type OpArgs = (u64, u64, u64, MemPort, u64, u8);

type CalcStepResult = (
    RamState,
    CalcIntermediateTypes,
    bool, bool,
);

fn calc_step<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    ev: &mut CachingEvaluator<'a, '_, eval::Public>,
    privilege_levels: bool,
    calc_step_func: Function<'a>,
    calc_step_inner_cases: &[(Bits<'a>, Function<'a>)],
    idx: usize,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    advice: TWire<'a, u64>,
    s1: &TWire<'a, RamState>,
    kmem: &mut KnownMem<'a>,
) -> (TWire<'a, RamState>, CalcIntermediate<'a>) {
    let opcode = ev.eval_typed(b.circuit(), instr.opcode).and_then(Opcode::from_raw);
    if opcode.is_some() || !b.circuit().allow_functions() {
        return calc_step_inner(
            cx, b, ev, calc_step_inner_cases, privilege_levels, idx, opcode, instr, mem_port, advice, s1, kmem);
    }

    // The opcode is unknown, so it could be performing any store at any address.
    kmem.clear();

    let c = b.circuit();
    let args_typed = TWire::<CalcStepArgs>::new((instr, mem_port.clone(), advice, s1.clone()));
    let num_regs = s1.regs.len();
    let (args_wires, args_sizes) = typed::to_wire_list(&args_typed);
    let w = c.call(
        calc_step_func, c.wire_list(&args_wires), &[], |_, s: &MultiExecWitness, _| s.into());

    let num_result_wires = CalcStepResult::expected_num_wires(&mut args_sizes.iter().copied());
    let result_wires = (0..num_result_wires).map(|i| c.extract(w, i)).collect::<Vec<_>>();
    // There are no variable-sized data structures in any of the input or output types except
    // `RamState`, and there is one `RamState` in the input and one in the output, so the output
    // sizes should be the same as the input sizes.
    let result = typed::from_wire_list::<CalcStepResult>(c.as_base(), &result_wires, &args_sizes);

    let (
        s2,
        ci,
        asserts_ok, found_bug,
    ) = result.repr;
    let (x, y, result, label_x, label_y_joined, label_result, addr_offset, mem_op_addr) = ci.repr;
    let ci = CalcIntermediate {
        x, y, result,
        tainted: IfMode::new(|pf| TaintCalcIntermediate {
            label_x: label_x.unwrap(&pf),
            label_y_joined: label_y_joined.unwrap(&pf),
            label_result: label_result.unwrap(&pf),
            addr_offset: addr_offset.unwrap(&pf),
        }),
        mem_port_unused: false,
        mem_op_addr,
    };
    wire_assert!(cx, b, asserts_ok, "assert failed in step {}", idx);
    wire_bug_if!(cx, b, found_bug, "found bug in step {}", idx);

    (s2, ci)
}

pub fn define_calc_step_function<'a>(
    b: &impl Builder<'a>,
    calc_step_inner_cases: &[(Bits<'a>, Function<'a>)],
    num_regs: usize,
    privilege_levels: bool,
) -> Function<'a> {
    struct CalcStepFunction<'a, 'b> {
        calc_step_inner_cases: &'b [(Bits<'a>, Function<'a>)],
        num_regs: usize,
        privilege_levels: bool,
    }

    impl<'a, 'b> DefineFunction<'a> for CalcStepFunction<'a, 'b> {
        fn build_body<C>(self, c: &C, args_wires: &[Wire<'a>]) -> Wire<'a>
        where C: CircuitTrait<'a> {
            let sizes = [self.num_regs, self.num_regs];
            let args = typed::from_wire_list::<CalcStepArgs>(c.as_base(), &args_wires, &sizes);
            let (instr, mem_port, advice, s1) = args.repr;

            let cx = Context::new(c);
            let b = BuilderImpl::from_ref(c);
            let mut ev = CachingEvaluator::<eval::Public>::new();
            let idx = 0;
            let mut kmem = KnownMem::with_default(b.lit(0));

            let (s2, ci) = calc_step_inner(
                &cx,
                b,
                &mut ev,
                self.calc_step_inner_cases,
                self.privilege_levels,
                idx,
                None,
                instr,
                &mem_port,
                advice,
                &s1,
                &mut kmem,
            );

            let (asserts, bugs) = cx.finish(c);
            let result = (
                s2,
                TWire::new((
                    ci.x,
                    ci.y,
                    ci.result,
                    TWire::new(ci.tainted.as_ref().map(|t| t.label_x.clone())),
                    TWire::new(ci.tainted.as_ref().map(|t| t.label_y_joined.clone())),
                    TWire::new(ci.tainted.as_ref().map(|t| t.label_result.clone())),
                    TWire::new(ci.tainted.as_ref().map(|t| t.addr_offset.clone())),
                    ci.mem_op_addr,
                )),
                TWire::new(c.all_true(asserts.iter().map(|tw| tw.repr))),
                TWire::new(c.any_true(bugs.iter().map(|tw| tw.repr))),
            );
            let (result_wires, _result_sizes) =
                typed::to_wire_list(&TWire::<CalcStepResult>::new(result));

            c.pack(&result_wires)
        }
    }

    let c = b.circuit();
    let sizes = [num_regs, num_regs];
    let num_args = CalcStepArgs::expected_num_wires(&mut sizes.iter().copied());
    let mut arg_tys = Vec::with_capacity(num_args);
    CalcStepArgs::for_each_expected_wire_type(c, &mut sizes.iter().copied(), |t| arg_tys.push(t));
    c.define_function_unchecked::<MultiExecWitness, _>("calc_step", &arg_tys,
        CalcStepFunction { calc_step_inner_cases, num_regs, privilege_levels })
}

fn op_and<'a>(
    b: &impl Builder<'a>,
    x: TWire<'a, u64>,
    y: TWire<'a, u64>,
    dest: TWire<'a, u8>,
) -> TWire<'a, (u64, u8)> {
    TWire::new((b.and(x, y), dest))
}

fn privileged_addr<'a>(
    b: &impl Builder<'a>,
    privilege_levels: bool,
    pc: TWire<'a, u64>,
    y: TWire<'a, u64>,
) -> TWire<'a, u64> {
    if privilege_levels {
        // Mask for jump and load/store addresses.  All bits are one except for bit 31, which
        // matches bit 31 of the PC.
        let addr_mask = b.or(pc, b.lit(0xffff_ffff_7fff_ffff_u64));
        b.and(y, addr_mask)
    } else {
        y
    }
}

fn op_jmp<'a>(
    b: &impl Builder<'a>,
    privilege_levels: bool,
    pc: TWire<'a, u64>,
    y: TWire<'a, u64>,
) -> TWire<'a, (u64, u8)> {
    let y_addr = privileged_addr(b, privilege_levels, pc, y);
    TWire::new((y_addr, b.lit(REG_PC)))
}

fn op_load<'a>(
    b: &impl Builder<'a>,
    pub_load_args: Option<(
        &mut CachingEvaluator<'a, '_, eval::Public>,
        &mut KnownMem<'a>,
        bool,
        TWire<'a, u64>,
        TWire<'a, u64>,
        &mut bool
    )>,
    mem_port: &TWire<'a, MemPort>,
    w: MemOpWidth,
    dest: TWire<'a, u8>,
) -> TWire<'a, (u64, u8)> {
    let known_value = if let Some((ev, kmem, privilege_levels, pc, y, mem_port_unused)) = pub_load_args {
        let y_addr = privileged_addr(b, privilege_levels, pc, y);
        kmem.load(b, ev, y_addr, w).map(|v| (v, mem_port_unused))
    } else {
        None
    };
    let result = if let Some((known_value, mem_port_unused)) = known_value {
        *mem_port_unused = true;
        known_value
    } else {
        extract_bytes_at_offset(b, mem_port.repr.value, mem_port.repr.addr, w)
    };
    TWire::new((result, dest))
}
    

// TODO(isweet): Consider renaming this to something less verbose like `define_opcodes`
// Produces a vector of each `Opcode`'s discriminant value and `circuit::Function` interpretation.
pub fn define_calc_step_inner_cases<'a>(
    b: &impl Builder<'a>,
    privilege_levels: bool,
) -> Vec<(Bits<'a>, Function<'a>)> {
    let c = b.circuit();

    let mut cases = Vec::new();
    macro_rules! case {
        ($op:expr, $Name:ident, $body:expr) => {
            struct $Name {
                privilege_levels: bool,
            }

            impl<'b> DefineFunction<'b> for $Name {
                fn build_body<C: CircuitTrait<'b>>(self, c: &C, args_wires: &[Wire<'b>]) -> Wire<'b> {
                    let b = BuilderImpl::from_ref(c);
                    let args = typed::from_wire_list::<OpArgs>(c.as_base(), &args_wires, &[]);
                    let (x, y, pc, mem_port, advice, dest) = args.repr;
                    let result = $body(b, self.privilege_levels, x, y, pc, &mem_port, advice, dest);
                    let (result_wires, _result_sizes) = typed::to_wire_list(&result);
                    c.pack(&result_wires)
                }
            }

            let discriminant = c.bits(Ty::uint(8), $op as u8);
            let num_args = OpArgs::expected_num_wires(&mut iter::empty());
            let mut arg_tys = Vec::with_capacity(num_args);
            OpArgs::for_each_expected_wire_type(c, &mut iter::empty(), |t| arg_tys.push(t));
            let k = c.define_function::<(), _>(stringify!($Name), &arg_tys, $Name { privilege_levels });

            cases.push((discriminant, k));
        };
    }

    case!(Opcode::And, OpAnd, |b, _, x, y, _, _, _, dest| op_and(b, x, y, dest));
    case!(Opcode::Jmp, OpJmp, |b, privilege_levels, _, y, pc, _, _, _| op_jmp(b, privilege_levels, pc, y));
    case!(Opcode::Load1, OpLoad1, |b, _, _, _, _, mem_port, _, dest| op_load(b, None, mem_port, MemOpWidth::W1, dest));

    cases
    // TODO(isweet): All the other opcodes
}

fn calc_step_inner<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    ev: &mut CachingEvaluator<'a, '_, eval::Public>,
    calc_step_inner_cases: &[(Bits<'a>, Function<'a>)],
    privilege_levels: bool,
    idx: usize,
    opcode: Option<Opcode>,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    advice: TWire<'a, u64>,
    s1: &TWire<'a, RamState>,
    kmem: &mut KnownMem<'a>,
) -> (TWire<'a, RamState>, CalcIntermediate<'a>) {
    let _g = b.scoped_label("calc_step");
    let c = b.circuit();

    let mut cases = Vec::new();
    macro_rules! case {
        ($op:expr, $body:expr) => {{
            if opcode.is_none() && !c.allow_functions() || opcode == Some($op) {
                let discriminant = $op;
                let result = $body;

                cases.push((discriminant, result));
            }
        }};
    }

    let x = b.index(&s1.regs, instr.op1, |b, i| b.lit(i as u8));
    let y = operand_value(b, s1, instr.op2, instr.imm);

    // This flag is set if the `MemPort` is publicly known to be unused.  `Load*` ops may set this
    // if `opcode` is known; otherwise, all non-memory ops set this below.
    let mut mem_port_unused = false;

    case!(Opcode::And, op_and(b, x, y, instr.dest));
    case!(Opcode::Jmp, op_jmp(b, privilege_levels, s1.pc, y));
    
    let pub_load_args = opcode.map(|_| (ev, &mut *kmem, privilege_levels, s1.pc, y, &mut mem_port_unused));    
    case!(Opcode::Load1, op_load(b, pub_load_args, mem_port, MemOpWidth::W1, instr.dest));

    let (result, dest) = if opcode.is_some() {
        if cases.len() == 1 {
            cases[0].1.repr
        } else {
            (b.lit(0), b.lit(REG_NONE))
        }
    } else if c.allow_functions() {
        let c = b.circuit();
        let discriminee = instr.opcode.repr;
        let cases = calc_step_inner_cases.iter().map(|(discriminant, k)| c.switch_case(*discriminant, *k, &[], |_, s: &(), _| s.into())).collect::<Vec<_>>();
        let args = [x.repr, y.repr, s1.pc.repr, /*(*mem_port).repr,*/ advice.repr, instr.dest.repr];
        let r = c.switch(discriminee, c.switch_case_list(&cases), c.wire_list(&args));
        let (result, dest) = typed::from_wire_list::<(u64, u8)>(c.as_base(), &[r], &[]).repr; // TODO(isweet): Confirm this is correct understanding of typed `pack`
        (result, dest)
    } else {
        let cases = cases.iter().map(|(discriminant, v)| TWire::<(_, _)>::new((b.eq(b.lit(*discriminant as u8), instr.opcode), *v))).collect::<Vec<_>>();
        b.mux_multi(&cases, b.lit((0, REG_NONE))).repr
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
        // TODO(isweet): Factor `y_addr` back into this function
        mem_op_addr: privileged_addr(b, privilege_levels, s1.pc, y),
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

type CheckStepArgs = (
    u32, bool, RamInstr, MemPort,
    CalcIntermediateTypes,
);

type CheckStepResult = (
    bool, bool,
);

fn check_step<'a>(
    cx: &Context<'a>,
    b: &impl Builder<'a>,
    check_step_func: Function<'a>,
    seg_idx: usize,
    idx: usize,
    cycle: TWire<'a, u32>,
    live: TWire<'a, bool>,
    instr: TWire<'a, RamInstr>,
    mem_port: TWire<'a, MemPort>,
    calc_im: &CalcIntermediate<'a>,
) {
    if !b.circuit().allow_functions() {
        return check_step_inner(cx, b, seg_idx, idx, cycle, live, instr, mem_port, calc_im);
    }

    let c = b.circuit();
    let args_typed = TWire::<CheckStepArgs>::new((
        cycle, live, instr, mem_port,
        TWire::new((
            calc_im.x,
            calc_im.y,
            calc_im.result,
            TWire::new(calc_im.tainted.as_ref().map(|t| t.label_x.clone())),
            TWire::new(calc_im.tainted.as_ref().map(|t| t.label_y_joined.clone())),
            TWire::new(calc_im.tainted.as_ref().map(|t| t.label_result.clone())),
            TWire::new(calc_im.tainted.as_ref().map(|t| t.addr_offset.clone())),
            calc_im.mem_op_addr,
        )),
    ));
    let (args_wires, args_sizes) = typed::to_wire_list(&args_typed);
    let w = c.call(
        check_step_func, c.wire_list(&args_wires), &[], |_, s: &(), _| s.into());

    let num_result_wires = CheckStepResult::expected_num_wires(&mut iter::empty());
    let result_wires = (0..num_result_wires).map(|i| c.extract(w, i)).collect::<Vec<_>>();
    let result = typed::from_wire_list::<CheckStepResult>(c.as_base(), &result_wires, &args_sizes);

    let (asserts_ok, found_bug) = result.repr;
    wire_assert!(cx, b, asserts_ok, "assert failed in segment {}, step {}", seg_idx, idx);
    wire_bug_if!(cx, b, found_bug, "found bug in segment {}, step {}", seg_idx, idx);
}

pub fn define_check_step_function<'a>(
    b: &impl Builder<'a>,
) -> Function<'a> {
    struct CheckStepFunction;

    impl<'b> DefineFunction<'b> for CheckStepFunction {
        fn build_body<C>(self, c: &C, args_wires: &[Wire<'b>]) -> Wire<'b>
        where C: CircuitTrait<'b> {
            let args = typed::from_wire_list::<CheckStepArgs>(c.as_base(), &args_wires, &[]);
            let (cycle, live, instr, mem_port, ci) = args.repr;
            let (
                x, y, result, label_x, label_y_joined, label_result, addr_offset, mem_op_addr,
            ) = ci.repr;
            let ci = CalcIntermediate {
                x, y, result,
                tainted: IfMode::new(|pf| TaintCalcIntermediate {
                    label_x: label_x.unwrap(&pf),
                    label_y_joined: label_y_joined.unwrap(&pf),
                    label_result: label_result.unwrap(&pf),
                    addr_offset: addr_offset.unwrap(&pf),
                }),
                mem_port_unused: false,
                mem_op_addr,
            };

            let cx = Context::new(c);
            let b = BuilderImpl::from_ref(c);
            let seg_idx = 0;
            let idx = 0;

            check_step_inner(
                &cx,
                b,
                seg_idx,
                idx,
                cycle,
                live,
                instr,
                mem_port,
                &ci,
            );

            let (asserts, bugs) = cx.finish(c);
            let result = (
                TWire::new(c.all_true(asserts.iter().map(|tw| tw.repr))),
                TWire::new(c.any_true(bugs.iter().map(|tw| tw.repr))),
            );
            let (result_wires, _result_sizes) =
                typed::to_wire_list(&TWire::<CheckStepResult>::new(result));

            c.pack(&result_wires)
        }
    }

    let c = b.circuit();
    let num_args = CheckStepArgs::expected_num_wires(&mut iter::empty());
    let mut arg_tys = Vec::with_capacity(num_args);
    CheckStepArgs::for_each_expected_wire_type(c, &mut iter::empty(), |t| arg_tys.push(t));
    c.define_function::<(), _>("check_step", &arg_tys, CheckStepFunction)
}

fn check_step_inner<'a>(
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

        let addr = calc_im.mem_op_addr;

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


pub struct InstrLookup<'b> {
    /// Maps start address to segment.
    index: BTreeMap<u64, &'b CodeSegment>,
    /// Default `RamInstr` to use for unallocated space.
    padding: RamInstr,
}

impl<'b> InstrLookup<'b> {
    pub fn new(prog: &'b [CodeSegment]) -> InstrLookup<'b> {
        InstrLookup {
            index: prog.iter().map(|cs| (cs.start, cs)).collect(),
            padding: fetch::PADDING_INSTR,
        }
    }
}

impl Index<u64> for InstrLookup<'_> {
    type Output = RamInstr;

    fn index(&self, idx: u64) -> &RamInstr {
        let (&start, cs) = match self.index.range(..= idx).next_back() {
            Some(x) => x,
            None => return &self.padding,
        };
        debug_assert!(start <= idx);
        let i = usize::try_from(idx - start).unwrap();
        if i >= cs.instrs.len() {
            return &self.padding;
        }
        &cs.instrs[i]
    }
}
