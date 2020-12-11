
use crate::ir::typed::{TWire, Builder};
use crate::micro_ram::context::Context;
use crate::micro_ram::types::{
    Execution, RamInstr, RamState, RamStateRepr, MemPort, MemOpKind, Opcode, Advice, operand_value,
};
use crate::{wire_assert, wire_bug_if};

pub const INITIALIZED: u64 = 0;

fn is_uninitialized<'a>(
    b: &Builder<'a>,
    w: TWire<'a,u64>
) -> TWire<'a,bool> {
    b.neq_zero(w)
}

// TODO: Use Repr?
pub struct TaintState<'a> {
    shadow_regs : Vec<TWire<'a, u64>>,
}

pub fn initialize<'a>(
    b: &Builder<'a>,
    exec: &'a Execution,
) -> TaintState<'a> {
    let mut shadow_regs = Vec::with_capacity(exec.params.num_regs);
    for i in 0..exec.params.num_regs {
        shadow_regs.push(b.lit(INITIALIZED));
    }
    TaintState{ shadow_regs }
}

// Encodes our taint semantics. 
pub fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    // calc_im: &CalcIntermediate<'a>,
    ts: &mut TaintState<'a>,
) {
    let prev_regs = &ts.shadow_regs;

    // TODO: Generalize this w/ the code in main.
    let mut cases = Vec::new();
    let mut add_case = |op, result, dest| {
        let op_match = b.eq(b.lit(op as u8), instr.opcode);
        let parts = TWire::<(_, _)>::new((result, dest));
        cases.push(TWire::<(_, _)>::new((op_match, parts)));
    };

    let x = b.index(&prev_regs, instr.op1, |b, i| b.lit(i as u8));
    let y = operand_value(b, prev_regs, instr.op2, instr.imm);

    // TODO: On load, check if port is poisoned.
    // TODO: Add required asserts (in mem?).

    {
        add_case(Opcode::Mov, y, instr.dest);
    }

    // Fall through to initialized.
    let (result, dest) = *b.mux_multi(&cases, TWire::<(_, _)>::new((b.lit(INITIALIZED), instr.dest)));

    let mut regs = Vec::with_capacity(prev_regs.len());
    for (i, &v_old) in prev_regs.iter().enumerate() {
        let is_dest = b.eq(b.lit(i as u8), dest);
        regs.push(b.mux(is_dest, result, v_old));
    }

    ts.shadow_regs = regs;

    // A leak is detected if there's a sink with uninitialized data.
    wire_bug_if!(
        cx, b.and(b.eq(instr.opcode, b.lit(Opcode::Sink as u8)), b.neq_zero(y)),
        "leak of uninitialized data from abstract register {:x} on cycle {}",
        cx.eval(y), cycle,
    );
}

