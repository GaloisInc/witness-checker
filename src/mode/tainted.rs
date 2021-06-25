
use crate::gadget::bit_pack;
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::{
    context::{Context, ContextWhen},
    types::{ByteOffset, CalcIntermediate, Label, MemOpWidth, MemPort, Opcode, PackedLabel, RamInstr, REG_NONE, TaintCalcIntermediate, WORD_BYTES}
};
use crate::mode::if_mode::{check_mode, self, IfMode, AnyTainted};
use crate::{wire_assert, wire_bug_if};

pub const UNTAINTED: Label = Label(3);
pub const PACKED_UNTAINTED: PackedLabel = 0xFFFF;
pub const LABEL_BITS: u8 = 2;

// Computes the meet (greatest lower bound) of two labels.
// Assumes that the label is valid.
fn meet<'a>(
    b: &Builder<'a>,
    l1: TWire<'a, Label>,
    l2: TWire<'a, Label>,
) -> TWire<'a, Label> {
    b.mux(b.eq(l1, l2), l1, b.lit(UNTAINTED))
}

// pub struct CalcIntermediate<'a> {

// Builds the circuit that calculates our conservative dynamic taint tracking semantics. 
pub fn calc_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    idx: usize,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    regs0: &IfMode<AnyTainted, Vec<TWire<'a,Label>>>,
    concrete_y: TWire<'a, u64>,
    concrete_dest: TWire<'a, u8>,
) -> (IfMode<AnyTainted, Vec<TWire<'a,Label>>>, IfMode<AnyTainted, TaintCalcIntermediate<'a>>) {
    if let Some(pf) = check_mode::<AnyTainted>() {
        let regs0 = regs0.as_ref().unwrap(&pf);
        let _g = b.scoped_label(format_args!("tainted::calc_step/cycle {}", idx));

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

        // Load1, Load2, Load4, Load8
        for w in MemOpWidth::iter() {
            let packed_labels = mem_port.tainted.unwrap(&pf);
            // TODO: Pull out offset and extracted labels in TaintCalcIntermediate?
            let offset = b.cast(bit_pack::extract_low::<ByteOffset>(b, mem_port.addr.repr));
            let label_parts = unpack_labels(b, packed_labels);
            let result = meet_labels_at_offset(b, label_parts, offset, w);
            add_case(w.load_opcode(), result);
        }

        // Stores??

        {
            // Check that the label is valid before truncating it.
            let label = cx.when(b, b.eq(instr.opcode, b.lit(Opcode::Taint as u8)), |cx| {
                convert_to_label(cx, b, idx, concrete_y)
            });
            add_case(Opcode::Taint, label);
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

        let timm = TaintCalcIntermediate {
            label_x: tx,
            label_result: result,
        };
        (IfMode::some(&pf, regs), IfMode::some(&pf, timm))
    } else {
        // JP: Better combinator for this? map_with_or?
        (IfMode::none(), IfMode::none())
    }
}

fn convert_to_label<'a,'b>(
    cx: &ContextWhen<'a,'b>,
    b: &Builder<'a>,
    idx: usize,
    label: TWire<'a, u64>, // Label>,
) -> TWire<'a, Label> {
    wire_assert!(
        cx, b.le(label, b.lit(UNTAINTED.0 as u64)),
        "Invalid tainted label {} at cycle {}",
        cx.eval(label), idx,
    );

    b.cast(label)
}

// Packs a Label into a PackedLabel. Assumes that the Label is already valid (2 bits long).
fn pack_label<'a>(
    b: &Builder<'a>,
    label: TWire<'a, Label>,
    offset: TWire<'a, u8>,
    width: TWire<'a, MemOpWidth>,
) -> TWire<'a, PackedLabel> {
    let label = b.cast::<_, PackedLabel>(label);

    let mut acc: TWire<'a, PackedLabel> = label;
    let mut packed = b.lit(0);
    for w in MemOpWidth::iter() {
        packed = b.mux(b.eq(width, b.lit(w)), acc, packed);
        acc = b.or(b.shl(acc, b.lit(LABEL_BITS * w.bytes() as u8)), acc);
    }

    // Offset in bits is position * LABEL_BITS.
    let offset = b.mul(offset, b.lit(LABEL_BITS));
    b.shl(packed, offset)
}

fn meet_labels_at_offset<'a>(
    b: &Builder<'a>,
    labels: [TWire<'a, Label>; WORD_BYTES],
    offset: TWire<'a, u8>, // ByteOffset>,
    width: MemOpWidth,
) -> TWire<'a,Label> {
    // We know the label at offset will be in the result, so
    // use that as the initial label (l == l `meet` l).
    // JP: Is there a way we can do a foldr1?
    let mut acc = b.index(&labels, offset, |b, idx| {
        // b.lit(ByteOffset::new(idx as u8))
        b.lit(idx as u8)
    });
    for (idx, &l) in labels.iter().enumerate() {
        let ignore = should_ignore(b, b.lit(idx as u8), offset, b.lit(width));
        acc = b.mux(ignore, acc, meet(b, l, acc));
    }
    acc
}

// TODO: Refactor to mux over the width first?
fn eq_packed_labels_at_offset<'a>(
    b: &Builder<'a>,
    offset: TWire<'a, u8>,
    width: TWire<'a, MemOpWidth>,
    label1: TWire<'a, PackedLabel>,
    label2: TWire<'a, PackedLabel>,
) -> TWire<'a, bool> {
    // Split into labels.
    let label1_parts = unpack_labels(b, label1);
    let label2_parts = unpack_labels(b, label2);

    let mut acc = b.lit(true);
    for (idx, (&v1, &v2)) in label1_parts.iter().zip(label2_parts.iter()).enumerate() {
        let idx = b.lit(idx as u8);
        let ignored = should_ignore(b, idx, offset, width);
        acc = b.and(acc, b.mux(ignored, b.lit(true), b.eq(v1, v2)));
    }
    acc
}

fn eq_packed_labels_except_at_offset<'a>(
    b: &Builder<'a>,
    offset: TWire<'a, u8>,
    width: TWire<'a, MemOpWidth>,
    label1: TWire<'a, PackedLabel>,
    label2: TWire<'a, PackedLabel>,
) -> TWire<'a, bool> {
    // Split into labels.
    let label1_parts = unpack_labels(b, label1);
    let label2_parts = unpack_labels(b, label2);

    let mut acc = b.lit(true);
    for (idx, (&v1, &v2)) in label1_parts.iter().zip(label2_parts.iter()).enumerate() {
        let idx = b.lit(idx as u8);
        let ignored = b.not(should_ignore(b, idx, offset, width));
        acc = b.and(acc, b.mux(ignored, b.lit(true), b.eq(v1, v2)));
    }
    acc
}

// Checks if the byte at index idx should be ignored.
fn should_ignore<'a>(
    b: &Builder<'a>,
    idx: TWire<'a, u8>,
    offset: TWire<'a, u8>,
    width: TWire<'a, MemOpWidth>,
) -> TWire<'a, bool> {
    let width = b.shl(b.lit(1 as u8), b.cast(width));
    // Check if ignored: idx < offset || idx >= offset + width
    b.or(b.lt(idx, offset), b.ge(idx, b.add(offset, width)))
}

fn unpack_labels<'a>(
    b: &Builder<'a>,
    labels: TWire<'a, PackedLabel>,
) -> [TWire<'a, Label>; WORD_BYTES] {
    // TODO: How do we split a u16 into Labels?
    let label_parts = bit_pack::split_bits::<[Label; WORD_BYTES]>(b, labels.repr);
    // let label_parts = bit_pack::split_bits::<[U2; WORD_BYTES]>(b, labels.repr);
    let mut labels = [b.lit(UNTAINTED); WORD_BYTES];
    for (idx, &l) in label_parts.iter().enumerate() {
        labels[idx] = l;
    }
    labels
}

pub fn check_state<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    calc_regs: &IfMode<AnyTainted, Vec<TWire<'a,Label>>>,
    trace_regs: &IfMode<AnyTainted, Vec<TWire<'a,Label>>>,
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
    init_regs: &IfMode<AnyTainted, Vec<TWire<'a,Label>>>,
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
    idx: usize, //  TODO: Not cycle anymore?
    instr: TWire<'a, RamInstr>,
    calc_im: &CalcIntermediate<'a>,
) {
    if let Some(pf) = check_mode::<AnyTainted>() {
        cx.when(b, b.eq(instr.opcode, b.lit(Opcode::Sink as u8)), |cx| {
            let y = convert_to_label(cx, b, idx, calc_im.y);
            let xt = calc_im.tainted.as_ref().unwrap(&pf).label_x;

            // A leak is detected if the label of data being output to a sink does not match the label of
            // the sink.
            wire_bug_if!(
                cx, b.and(b.ne(xt, y),b.ne(xt, b.lit(UNTAINTED))),
                "leak of tainted data from register {:x} with label {} does not match output channel label {} on cycle {}",
                cx.eval(instr.op1), cx.eval(xt), cx.eval(y), idx,
            );
        });
    }
}

// Circuit for checking memory operations. Only called when an operation is a memory operation
// (read, write, poison).
pub fn check_step_mem<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    idx: usize,
    mem_port: &TWire<'a, MemPort>, 
    is_store_like: &TWire<'a, bool>, 
    imm: &IfMode<AnyTainted, TaintCalcIntermediate<'a>>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let TaintCalcIntermediate{label_x: x_taint, label_result: result_taint} = imm.get(&pf);
        let expect_tainted = b.mux(*is_store_like, *x_taint, *result_taint);
        let port_tainted = mem_port.tainted.unwrap(&pf);

        let offset = b.cast::<_, u8>(bit_pack::extract_low::<ByteOffset>(b, mem_port.addr.repr));
        let expect_pack_tainted = pack_label(b, expect_tainted, offset, mem_port.width);

        let op = mem_port.op;
        let width = mem_port.width;
        wire_assert!(
            cx, eq_packed_labels_at_offset(b, offset, mem_port.width, port_tainted, expect_pack_tainted),
            "cycle {}'s mem port (op {:?}, offset {}, width {:?}) has tainted {:#x} expected {:#x} ({})",
            idx, cx.eval(op),
            cx.eval(offset), cx.eval(width),
            cx.eval(port_tainted),
            cx.eval(expect_pack_tainted), cx.eval(expect_tainted),
        );
    }
}

// Circuit that checks memory when port2 is a read. Since it is a read, port2's tainted must be the same as
// port1's tainted.
pub fn check_read_memports<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    port1label: &TWire<'a, IfMode<AnyTainted,PackedLabel>>,
    port2: &TWire<'a, MemPort>, 
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let tainted1 = port1label.unwrap(&pf);
        let tainted2 = port2.tainted.unwrap(&pf);

        let addr2 = port2.addr;
        let cycle2 = port2.cycle;
        wire_assert!(
            cx, b.eq(tainted1, tainted2),
            "tainted read from {:#x} on cycle {} produced {:#x} (expected {:#x})",
            cx.eval(addr2), cx.eval(cycle2),
            cx.eval(tainted2), cx.eval(tainted1),
        );
    }
}

// Circuit that checks memory when port is a write. Since it is a write, port's unmodified tainted bits must be the same as prev's.
pub fn check_write_memports<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    prev_label: &TWire<'a, IfMode<AnyTainted,PackedLabel>>,
    port: &TWire<'a, MemPort>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let tainted1 = prev_label.unwrap(&pf);
        let tainted2 = port.tainted.unwrap(&pf);

        let addr2 = port.addr;
        let cycle2 = port.cycle;

        let offset2 = b.cast(bit_pack::extract_low::<ByteOffset>(b, addr2.repr));
        let width2 = port.width;

        wire_assert!(
            cx, eq_packed_labels_except_at_offset(b, offset2, width2, tainted1, tainted2),
            "tainted write from {:x} on cycle {} modified outside width {:?}: 0x{:x} != 0x{:x}",
            cx.eval(addr2), cx.eval(cycle2),
            cx.eval(width2),
            cx.eval(tainted2), cx.eval(tainted1),
        );
    }
}
