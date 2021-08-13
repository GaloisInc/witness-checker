
use crate::gadget::bit_pack;
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::{
    context::{Context, ContextWhen},
    types::{ByteOffset, CalcIntermediate, Label, MemOpWidth, MemPort, Opcode, PACKED_UNTAINTED, PackedLabel, RamInstr, TaintCalcIntermediate, UNTAINTED, WORD_BYTES}
};
use crate::mode::if_mode::{check_mode, self, IfMode, AnyTainted};
use crate::{wire_assert, wire_bug_if};

// Builds the circuit that calculates our conservative dynamic taint tracking semantics. 
pub fn calc_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    idx: usize,
    instr: TWire<'a, RamInstr>,
    mem_port: &TWire<'a, MemPort>,
    regs0: &IfMode<AnyTainted, Vec<TWire<'a,PackedLabel>>>,
    concrete_y: TWire<'a, u64>,
    concrete_dest: TWire<'a, u8>,
) -> (IfMode<AnyTainted, Vec<TWire<'a,PackedLabel>>>, IfMode<AnyTainted, TaintCalcIntermediate<'a>>) {
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
        // If y is an immediate, set ty to PACKED_UNTAINTED.
        let reg_val = b.index(&regs0, instr.op2, |b, i| b.lit(i as u64));
        let ty = b.mux(instr.imm, b.lit(PACKED_UNTAINTED), reg_val);

        {
            add_case(Opcode::Mov, ty);
        }

        {
            // Reuse concrete computed dest.
            add_case(Opcode::Cmov, ty);
        }

        let offset = bit_pack::extract_low::<ByteOffset>(b, mem_port.addr.repr);

        // Load1, Load2, Load4, Load8
        for w in MemOpWidth::iter() {
            let packed_labels = mem_port.tainted.unwrap(&pf);
            // let label_parts = unpack_labels(b, packed_labels);
            // let result = meet_labels_at_offset(b, label_parts, offset, w);
            let result = take_width_at_offset(b, packed_labels, offset, w, UNTAINTED);
            add_case(w.load_opcode(), result);
        }

        // Stores are checked in check_step_mem.

        {
            // Check that the label is valid before truncating it.
            let label = cx.when(b, b.lit(true), |cx| { // TODO: Remove this when
                convert_to_label(cx, b, idx, concrete_y)
            });
            // Taint1, Taint2, Taint4, Taint8
            for w in MemOpWidth::iter() {
                let labels = duplicate(b, label, w, UNTAINTED);
                add_case(w.taint_opcode(), labels);
            }
        }

        // Fall through to mark destination as untainted.
        let result = b.mux_multi(&cases, b.lit(PACKED_UNTAINTED));

        let mut regs = Vec::with_capacity(regs0.len());
        for (i, &v_old) in regs0.iter().enumerate() {
            let is_dest = b.eq(b.lit(i as u8), concrete_dest);
            regs.push(b.mux(is_dest, result, v_old));
        }

        let timm = TaintCalcIntermediate {
            label_x: tx,
            label_result: result,
            addr_offset: offset,
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
    let l = b.cast(label);

    // Check that the label is valid by ensuring the casted label is unchanged.
    wire_assert!(
        cx, b.eq(label, b.cast(l)),
        "Invalid tainted label {} at cycle {}",
        cx.eval(label), idx,
    );

    l
}

// Duplicate a value `width` times. Fills the remaining elements with `default`.
fn duplicate<'a>(
    b: &Builder<'a>,
    label: TWire<'a, Label>,
    width: MemOpWidth,
    default: Label,
) -> TWire<'a, PackedLabel> {
    let default = b.lit(default);
    let mut res = [default; WORD_BYTES];
    for (idx, res) in res.iter_mut().enumerate() {
        // If idx < width, use label, otherwise use default.
        if idx < width.bytes() {
            *res = label.clone();
        }
    }
    TWire::new(res)
}

// Take `width` elements starting at the given offset. Fills the remaining elements with `default`.
fn take_width_at_offset<'a>(
    b: &Builder<'a>,
    labels: TWire<'a, PackedLabel>,
    offset: TWire<'a, ByteOffset>,
    width: MemOpWidth,
    default: Label,
) -> TWire<'a, PackedLabel> {
    // Move labels over by offset.
    let mut res = shift_labels(b, labels, offset, default);

    // Replace labels with position greater than width with default.
    let default = b.lit(default);
    for (idx, res) in res.repr.iter_mut().enumerate() {
        // If idx < width, use shifted value, otherwise use default.
        if idx >= width.bytes() {
            *res = default;
        }
    }

    res
}

// Shift right by `offset`, filling with `default`.
fn shift_labels<'a>(
    b: &Builder<'a>,
    labels: TWire<'a, PackedLabel>,
    offset: TWire<'a, ByteOffset>,
    default: Label,
) -> TWire<'a, PackedLabel> {
    let default = b.lit(default);
    let offset = b.cast(offset);
    let mut res = [default; WORD_BYTES];
    for (idx, res) in res.iter_mut().enumerate() {
        let pos = b.add(offset, b.lit(idx as u8));
        *res = b.index_with_default(&labels.repr, pos, default, |b, i| b.lit(i as u8));
    }

    TWire::new(res)
}

// Compare `width` labels.
fn eq_word_labels_with_width<'a>(
    b: &Builder<'a>,
    width: TWire<'a, MemOpWidth>,
    label1: TWire<'a, PackedLabel>,
    label2: TWire<'a, PackedLabel>,
) -> TWire<'a, bool> {
    let offset = b.lit(ByteOffset::new(0));

    let mut acc = b.lit(true);
    for (idx, (&v1, &v2)) in label1.repr.iter().zip(label2.repr.iter()).enumerate() {
        let idx = b.lit(idx as u8);
        let ignored = should_ignore(b, idx, offset, width);
        acc = b.and(acc, b.mux(ignored, b.lit(true), b.eq(v1, v2)));
    }
    acc
}

fn eq_packed_labels_except_at_offset<'a>(
    b: &Builder<'a>,
    offset: TWire<'a, ByteOffset>, // u8>,
    width: TWire<'a, MemOpWidth>,
    label1: TWire<'a, PackedLabel>,
    label2: TWire<'a, PackedLabel>,
) -> TWire<'a, bool> {
    let mut acc = b.lit(true);
    for (idx, (&v1, &v2)) in label1.repr.iter().zip(label2.repr.iter()).enumerate() {
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
    offset: TWire<'a, ByteOffset>,
    width: TWire<'a, MemOpWidth>,
) -> TWire<'a, bool> {
    let width = b.shl(b.lit(1 as u8), b.cast(width));
    let offset = b.cast(offset);
    // Check if ignored: idx < offset || idx >= offset + width
    b.or(b.lt(idx, offset), b.ge(idx, b.add(offset, width)))
}

pub fn check_state<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    cycle: u32,
    calc_regs: &IfMode<AnyTainted, Vec<TWire<'a,PackedLabel>>>,
    trace_regs: &IfMode<AnyTainted, Vec<TWire<'a,PackedLabel>>>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let _g = b.scoped_label(format_args!("tainted::check_state/cycle {}", cycle));

        let calc_regs = calc_regs.get(&pf);
        let trace_regs = trace_regs.get(&pf);

        for (i, (&v_calc, &v_new)) in calc_regs.iter().zip(trace_regs.iter()).enumerate() {
            wire_assert!(
                cx, b.eq(v_new, v_calc),
                "cycle {} sets tainted label of reg {} to {:?} (expected {:?})",
                cycle, i, cx.eval(v_new), cx.eval(v_calc),
            );
        }
    }
}

pub fn check_first<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    init_regs: &IfMode<AnyTainted, Vec<TWire<'a,PackedLabel>>>,
) {
    if let Some(init_regs) = init_regs.try_get() {
        for (i, &r) in init_regs.iter().enumerate() {
            wire_assert!(
                cx, b.eq(r, b.lit(PACKED_UNTAINTED)),
                "initial tainted r{} has value {:?} (expected {:?})",
                i, cx.eval(r), PACKED_UNTAINTED,
            );
        }
    }
}

pub fn check_step<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    seg_idx: usize,
    idx: usize,
    instr: TWire<'a, RamInstr>,
    calc_im: &CalcIntermediate<'a>,
) {
    if let Some(pf) = check_mode::<AnyTainted>() {
        // Sink1, Sink2, Sink4, Sink8
        for w in MemOpWidth::iter() {
            cx.when(b, b.eq(instr.opcode, b.lit(w.sink_opcode() as u8)), |cx| {
                let y = convert_to_label(cx, b, idx, calc_im.y);
                let xts = calc_im.tainted.as_ref().unwrap(&pf).label_x;

                // Iterate over labels of xts.
                for (idx, &xt) in xts.repr.iter().enumerate() {

                    // When the position is relevant, check for sink.
                    if idx < w.bytes() {

                        // A leak is detected if the label of data being output to a sink does not match the label of
                        // the sink.
                        wire_bug_if!(
                            cx, b.and(b.ne(xt, y),b.ne(xt, b.lit(UNTAINTED))),
                            "leak of tainted data from register {:x} with label {} does not match output channel label {} on cycle {},{}",
                            cx.eval(instr.op1), cx.eval(xt), cx.eval(y), seg_idx, idx,
                        );
                    }
                }
            });
        }
    }
}

// Circuit for checking memory operations. Only called when an operation is a memory operation
// (read, write, poison).
pub fn check_step_mem<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    seg_idx: usize,
    idx: usize,
    mem_port: &TWire<'a, MemPort>, 
    is_store_like: &TWire<'a, bool>, 
    imm: &IfMode<AnyTainted, TaintCalcIntermediate<'a>>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        cx.when(b, *is_store_like, |cx| {
            let TaintCalcIntermediate{label_x: x_taint, label_result: _result_taint, addr_offset: offset} = imm.get(&pf);
            let expect_tainted = *x_taint;
            let offset = *offset;
            let port_tainted = mem_port.tainted.unwrap(&pf);

            // Shift position by offset.
            let port_shifted = shift_labels(b, port_tainted, offset, UNTAINTED);

            let op = mem_port.op;
            let width = mem_port.width;
            // Compare the lowest `width` labels.
            wire_assert!(
                cx, eq_word_labels_with_width(b, mem_port.width, port_shifted, expect_tainted),
                "segment {}: step {}'s mem port (op {:?}, offset {:?}, width {:?}) has tainted {:?} expected {:?} ({:?})",
                seg_idx, idx, cx.eval(op),
                cx.eval(offset), cx.eval(width),
                cx.eval(port_tainted),
                cx.eval(expect_tainted), cx.eval(expect_tainted),
            );
        });
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
            "tainted read from {:#x} on cycle {} produced {:?} (expected {:?})",
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
    port2: &TWire<'a, MemPort>,
    offset2: &TWire<'a, ByteOffset>,
) {
    if let Some(pf) = if_mode::check_mode::<AnyTainted>() {
        let tainted1 = prev_label.unwrap(&pf);
        let tainted2 = port2.tainted.unwrap(&pf);

        let width2 = port2.width;
        let addr2 = port2.addr;
        let cycle2 = port2.cycle;
        wire_assert!(
            cx, eq_packed_labels_except_at_offset(b, *offset2, width2, tainted1, tainted2),
            "tainted write from {:x} on cycle {} modified outside width {:?}: 0x{:?} != 0x{:?}",
            cx.eval(addr2), cx.eval(cycle2),
            cx.eval(width2),
            cx.eval(tainted2), cx.eval(tainted1),
        );
    }
}
