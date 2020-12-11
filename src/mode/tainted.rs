
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::{
    context::{Context, ContextWhen},
    types::{MemPort, Opcode, RamInstr, operand_value}
};
use crate::mode::if_mode::{self, IfMode, AnyTainted};
use crate::wire_assert;

pub const UNTAINTED: u64 = u64::MAX;

// Builds the circuit that calculates our conservative dynamic taint tracking semantics. 
pub fn calc_step<'a>(
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    regs0: &IfMode<AnyTainted, Vec<TWire<'a,u64>>>
) -> (IfMode<AnyTainted, Vec<TWire<'a,u64>>>, IfMode<AnyTainted, (TWire<'a,u64>, TWire<'a,u64>)>) {
    unimplemented!{};
    // regs0.as_ref().map_with(|pf, regs0| {
    //     let _g = b.scoped_label(format_args!("tainted::calc_step/cycle {}", cycle));

    //     let mut cases = Vec::new();
    //     let mut add_case = |op, result, dest| {
    //         let op_match = b.eq(b.lit(op as u8), instr.opcode);
    //         let parts = TWire::<(_, _)>::new((result, dest));
    //         cases.push(TWire::<(_, _)>::new((op_match, parts)));
    //     };

    //     let x = b.index(&regs0, instr.op1, |b, i| b.lit(i as u8));
    //     let y = operand_value(b, regs0, instr.op2, instr.imm);

    //     // TODO: On load, check if port is tainted.
    //     // TODO: Add required asserts (in mem?). 

    //     {
    //         add_case(Opcode::Mov, y, instr.dest);
    //     }

    //     // Fall through to not tainted.
    //     let (result, dest) = *b.mux_multi(&cases, TWire::<(_, _)>::new((b.lit(UNTAINTED), instr.dest)));

    //     let mut regs = Vec::with_capacity(regs0.len());
    //     for (i, &v_old) in regs0.iter().enumerate() {
    //         let is_dest = b.eq(b.lit(i as u8), dest);
    //         regs.push(b.mux(is_dest, result, v_old));
    //     }

    //     regs
    // })
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
                "cycle {} sets tainted reg {} to {} (expected {})",
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

// Circuit for checking memory operations.
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

// Circuit when port2 is a read.
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

// check_mem, check_last, and check_first_mem are not needed???

