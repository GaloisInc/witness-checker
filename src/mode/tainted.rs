
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::{
    context::{Context, ContextWhen},
    types::{CalcIntermediate, MemPort, Opcode, RamInstr, REG_NONE}
};
use crate::mode::if_mode::{check_mode, self, IfMode, AnyTainted};
use crate::{wire_assert, wire_bug_if};

pub const UNTAINTED: u64 = u64::MAX;

// Builds the circuit that calculates our conservative dynamic taint tracking semantics. 
pub fn calc_step<'a>(
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    regs0: &IfMode<AnyTainted, Vec<TWire<'a,u64>>>,
    concrete_y: TWire<'a, u64>,
    concrete_dest: TWire<'a, u8>,
) -> (IfMode<AnyTainted, Vec<TWire<'a,u64>>>, IfMode<AnyTainted, (TWire<'a,u64>, TWire<'a,u64>)>) {
    if let Some(pf) = check_mode::<AnyTainted>() {
        let regs0 = regs0.as_ref().unwrap(&pf);
        let _g = b.scoped_label(format_args!("tainted::calc_step/cycle {}", cycle));

        let mut cases = Vec::new();
        let mut add_case = |op, result| {
            let op_match = b.eq(b.lit(op as u8), instr.opcode);
            let parts = result;
            cases.push(TWire::<_>::new((op_match, parts)));
        };

        // Extract the tainted label of x, y.
        let tx = b.index(&regs0, instr.op1, |b, i| b.lit(i as u8));
        // If y is an immediate, set ty to UNTAINTED.
        let reg_val = b.index(&regs0, instr.op2, |b, i| b.lit(i as u64));
        let ty = b.mux(instr.imm, b.lit(UNTAINTED), reg_val);

        {
            add_case(Opcode::Mov, ty);
        }

        {
            // Reuse concrete computed dest.
            add_case(Opcode::Cmov, ty);
        }

        {
            let result = mem_port.tainted.unwrap(&pf);
            add_case(Opcode::Load, result);
        }

        {
            add_case(Opcode::Taint, concrete_y);
        }

        /*
        // Don't taint REG_PC. Handles the cases where instruction destinations are REG_PC. 
        // JP: Is this necessary?

        {
            add_case(Opcode::Jmp, b.lit(UNTAINTED), b.lit(REG_NONE));
        }

        {
            add_case(Opcode::Cjmp, b.lit(UNTAINTED), b.lit(REG_NONE));
        }

        {
            add_case(Opcode::Cnjmp, b.lit(UNTAINTED), b.lit(REG_NONE));
        }

        {
            add_case(Opcode::Sink, b.lit(UNTAINTED), b.lit(REG_NONE));
        }

        {
            add_case(Opcode::Answer, b.lit(UNTAINTED), b.lit(REG_NONE));
        }

        {
            add_case(Opcode::Stutter, b.lit(UNTAINTED), b.lit(REG_NONE));
        }
        */

        // Fall through to mark destination as untainted.
        let result = b.mux_multi(&cases, b.lit(UNTAINTED));

        let mut regs = Vec::with_capacity(regs0.len());
        for (i, &v_old) in regs0.iter().enumerate() {
            let is_dest = b.eq(b.lit(i as u8), concrete_dest);
            regs.push(b.mux(is_dest, result, v_old));
        }

        (IfMode::some(&pf, regs), IfMode::some(&pf, (tx, result)))
    } else {
        // JP: Better combinator for this? map_with_or?
        (IfMode::none(), IfMode::none())
    }
}

pub fn check_state<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    calc_regs: &IfMode<AnyTainted, Vec<TWire<'a,u64>>>,
    trace_regs: &IfMode<AnyTainted, Vec<TWire<'a,u64>>>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let _g = b.scoped_label(format_args!("tainted::check_state/cycle {}", cycle));

        let calc_regs = calc_regs.get(&pf);
        let trace_regs = trace_regs.get(&pf);

        for (i, (&v_calc, &v_new)) in calc_regs.iter().zip(trace_regs.iter()).enumerate() {
            wire_assert!(
                cx, b.eq(v_new, v_calc),
                "cycle {} sets tainted label of reg {} to {} (expected {})",
                cycle, i, cx.eval(v_new), cx.eval(v_calc),
            );
        }
    }
}

pub fn check_first<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    init_regs: &IfMode<AnyTainted, Vec<TWire<'a,u64>>>,
) {
    if let Some(init_regs) = init_regs.try_get() {
        for (i, &r) in init_regs.iter().enumerate() {
            wire_assert!(
                cx, b.eq(r, b.lit(UNTAINTED)),
                "initial tainted r{} has value {} (expected {})",
                i, cx.eval(r), UNTAINTED,
            );
        }
    }
}

pub fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    calc_im: &CalcIntermediate<'a>,
) {
    if let Some(pf) = check_mode::<AnyTainted>() {
        let y = calc_im.y;
        let (xt, _) = calc_im.tainted.unwrap(&pf);

        // A leak is detected if the label of data being output to a sink does not match the label of
        // the sink.
        wire_bug_if!(
            cx, b.and(b.eq(instr.opcode, b.lit(Opcode::Sink as u8)), b.and(b.ne(xt, y),b.ne(xt, b.lit(UNTAINTED)))),
            "leak of tainted data from register {:x} with label {} does not match output channel label {} on cycle {}",
            cx.eval(instr.op1), cx.eval(xt), cx.eval(y), cycle,
        );
    }
}

// Circuit for checking memory operations. Only called when an operation is a memory operation
// (read, write, poison).
pub fn check_step_mem<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    cycle: u32,
    mem_port: &TWire<'a, MemPort>, 
    is_store_like: &TWire<'a, bool>, 
    imm: IfMode<AnyTainted, (TWire<'a,u64>, TWire<'a,u64>)>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let (x_taint, result_taint) = imm.get(&pf);
        let expect_tainted = b.mux(*is_store_like, *x_taint, *result_taint);
        let port_tainted : TWire<u64> = mem_port.tainted.unwrap(&pf);

        wire_assert!(
            cx, b.eq(port_tainted, expect_tainted),
            "cycle {}'s mem port (op {}) has tainted {} (expected {})",
            cycle, cx.eval(mem_port.op.repr), cx.eval(mem_port.tainted), cx.eval(expect_tainted),
        );
    }
}

// Circuit that checks memory when port2 is a read. Since it is a read, port2's tainted must be the same as
// port1's tainted.
pub fn check_memports<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    port1: &TWire<'a, MemPort>, 
    port2: &TWire<'a, MemPort>, 
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let tainted1 = port1.tainted.unwrap(&pf);
        let tainted2 = port2.tainted.unwrap(&pf);

        wire_assert!(
            cx, b.eq(tainted1, tainted2),
            "tainted read from {:x} on cycle {} produced {} (expected {})",
            cx.eval(port2.addr), cx.eval(port2.cycle),
            cx.eval(tainted2), cx.eval(tainted1),
        );
    }
}
// TODO: Need to check that reads/writes to tainted match op.

// check_mem, check_last, and check_first_mem are not needed???

