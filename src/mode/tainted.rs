
use crate::gadget::bit_pack;
use crate::ir::typed::{Builder, TWire};
use crate::micro_ram::{
    context::{Context, ContextWhen},
    types::{ByteOffset, CalcIntermediate, Label, MemOpWidth, MemPort, Opcode, WORD_BOTTOM, WordLabel, RamInstr, TaintCalcIntermediate, BOTTOM, MAYBE_TAINTED, WORD_BYTES, WORD_MAYBE_TAINTED}
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
    regs0: &IfMode<AnyTainted, Vec<TWire<'a,WordLabel>>>,
    concrete_x: TWire<'a, u64>,
    concrete_y: TWire<'a, u64>,
    concrete_dest: TWire<'a, u8>,
) -> (IfMode<AnyTainted, Vec<TWire<'a,WordLabel>>>, IfMode<AnyTainted, TaintCalcIntermediate<'a>>) {
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
        // If y is an immediate, set ty to WORD_UNTAINTED.
        let reg_val = b.index(&regs0, instr.op2, |b, i| b.lit(i as u64));
        let ty = b.mux(instr.imm, b.lit(WORD_BOTTOM), reg_val);

        let tx_joined = fold1_join_vec(b, tx);
        let ty_joined = fold1_join_vec(b, ty);

        {
            add_case(Opcode::Mov, ty);
        }

        // Extract the dest's previous tainted labels.
        let tdest = b.index(&regs0, instr.dest, |b, i| b.lit(i as u8));

        {
            // Recheck the conditional.
            let tbranch = b.mux(b.neq_zero(concrete_x), ty, tdest);

            // Join the conditional label with the branch's label.
            let t = map_join_vec(b, tx_joined, tbranch);

            // Reuse concrete computed dest.
            add_case(Opcode::Cmov, t);
        }

        {
            add_case(Opcode::Not, approx(b, ty_joined));
        }

        {
            let is_jmp = b.eq(instr.opcode, b.lit(Opcode::Jmp as u8));
            let is_cjmp  = b.eq(instr.opcode, b.lit(Opcode::Cjmp as u8));
            let is_cnjmp  = b.eq(instr.opcode, b.lit(Opcode::Cnjmp as u8));

            // Assert that we're not jumping to a tainted location.
            cx.when(b, b.or(b.or(is_jmp, is_cjmp), is_cnjmp), |cx| {
                wire_assert!(
                    cx, b.eq(ty_joined, b.lit(BOTTOM)),
                    "Invalid jump. Cannot jump to tainted destination {} with label {} at cycle {}",
                    cx.eval(concrete_y), cx.eval(ty_joined), idx,
                );
            });

            // Assert that the conditional is not tainted.
            cx.when(b, b.or(is_cjmp, is_cnjmp), |cx| {
                wire_assert!(
                    cx, b.eq(tx_joined, b.lit(BOTTOM)),
                    "Invalid jump. Cannot branch on tainted data with label {} at cycle {}",
                    cx.eval(tx_joined), idx,
                );
            });
        }

        let offset = bit_pack::extract_low::<ByteOffset>(b, mem_port.addr.repr);

        // Load1, Load2, Load4, Load8
        for w in MemOpWidth::iter() {
            let packed_labels = mem_port.tainted.unwrap(&pf);
            let labels = take_width_at_offset(b, packed_labels, offset, w, BOTTOM);
            // Check if the address is tainted.
            let result = check_vec(b, ty_joined, labels);
            add_case(w.load_opcode(), result);
        }

        // Stores are checked in check_step_mem.

        {
            // Check that the label is valid before truncating it.
            let label = cx.when(b, is_taint(b, instr.opcode), |cx| {
                convert_to_label(cx, b, idx, concrete_y)
            });

            // Taint1
            let mut labels = tdest.clone();
            labels[0] = label;
            add_case(Opcode::Taint1, labels);
        }

        // Fall through to the binop case since that is the most common.
        let binop_label = approx2(b, tx_joined, ty_joined);
        let result = b.mux_multi(&cases, binop_label);

        let mut regs = Vec::with_capacity(regs0.len());
        for (i, &v_old) in regs0.iter().enumerate() {
            let is_dest = b.eq(b.lit(i as u8), concrete_dest);
            regs.push(b.mux(is_dest, result, v_old));
        }

        let timm = TaintCalcIntermediate {
            label_x: tx,
            label_y_joined: ty_joined,
            label_result: result,
            addr_offset: offset,
        };
        (IfMode::some(&pf, regs), IfMode::some(&pf, timm))
    } else {
        // JP: Better combinator for this? map_with_or?
        (IfMode::none(), IfMode::none())
    }
}

fn join<'a>(
    b: &Builder<'a>,
    label1: TWire<'a,Label>,
    label2: TWire<'a,Label>,
) -> TWire<'a,Label> {
    let mt = b.lit(MAYBE_TAINTED);
    let bottom = b.lit(BOTTOM);

    let is_mt = b.or(b.eq(label1, mt), b.eq(label2, mt));
    let cases = [
        (is_mt, mt),
        (b.eq(label1, bottom), label2),
        (b.eq(label2, bottom), label1),
        (b.eq(label1, label2), label1),
    ];
    let cases: Vec<_> = cases.iter().map(|x| TWire::<_>::new(*x)).collect();

    b.mux_multi(&cases, mt)
}

fn map_join_vec<'a>(
    b: &Builder<'a>,
    label: TWire<'a,Label>,
    labels: TWire<'a,WordLabel>,
) -> TWire<'a,WordLabel> {
    let mut res = [b.lit(BOTTOM); WORD_BYTES];
    for (idx, res) in res.iter_mut().enumerate() {
        *res = join(b, label, labels[idx]);
    }

    TWire::new(res)
}

fn fold1_join_vec<'a>(
    b: &Builder<'a>,
    labels: TWire<'a,WordLabel>,
) -> TWire<'a,Label> {
    let mut res = labels[0];
    for l in labels.iter() {
        *res = *join(b, res, *l);
    }
    res
}

fn check_vec<'a>(
    b: &Builder<'a>,
    guard: TWire<'a,Label>,
    labels: TWire<'a,WordLabel>,
) -> TWire<'a,WordLabel> {
    b.mux(b.eq(guard, b.lit(BOTTOM)), labels, b.lit(WORD_MAYBE_TAINTED))
}

fn is_taint<'a>(
    b: &Builder<'a>,
    opcode: TWire<'a,u8>,
) -> TWire<'a, bool> {
    b.eq(opcode, b.lit(Opcode::Taint1 as u8))
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
) -> TWire<'a, WordLabel> {
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

fn approx<'a>(
    b: &Builder<'a>,
    label: TWire<'a, Label>,
) -> TWire<'a, WordLabel> {
    let bottom = b.lit(BOTTOM);
    let l = b.mux(b.eq(label, bottom), bottom, b.lit(MAYBE_TAINTED));
    duplicate(b, l, MemOpWidth::W8, BOTTOM)
}

fn approx2<'a>(
    b: &Builder<'a>,
    label1: TWire<'a, Label>,
    label2: TWire<'a, Label>,
) -> TWire<'a, WordLabel> {
    let bottom = b.lit(BOTTOM);
    let l = b.mux(b.and(b.eq(label1, bottom), b.eq(label2, bottom)), bottom, b.lit(MAYBE_TAINTED));
    duplicate(b, l, MemOpWidth::W8, BOTTOM)
}

// Take `width` elements starting at the given offset. Fills the remaining elements with `default`.
fn take_width_at_offset<'a>(
    b: &Builder<'a>,
    labels: TWire<'a, WordLabel>,
    offset: TWire<'a, ByteOffset>,
    width: MemOpWidth,
    default: Label,
) -> TWire<'a, WordLabel> {
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
    labels: TWire<'a, WordLabel>,
    offset: TWire<'a, ByteOffset>,
    default: Label,
) -> TWire<'a, WordLabel> {
    // TODO: Could optimize this.
    // https://gitlab-ext.galois.com/fromager/cheesecloth/witness-checker/-/merge_requests/19#note_91033
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
    label1: TWire<'a, WordLabel>,
    label2: TWire<'a, WordLabel>,
) -> TWire<'a, bool> {
    let offset = b.lit(ByteOffset::new(0));

    let mut acc = b.lit(true);
    for (idx, (&v1, &v2)) in label1.repr.iter().zip(label2.repr.iter()).enumerate() {
        let idx = b.lit(idx as u8);
        let ignored = in_range(b, idx, offset, width);
        acc = b.and(acc, b.mux(ignored, b.lit(true), b.eq(v1, v2)));
    }
    acc
}

fn eq_packed_labels_except_at_offset<'a>(
    b: &Builder<'a>,
    offset: TWire<'a, ByteOffset>,
    width: TWire<'a, MemOpWidth>,
    label1: TWire<'a, WordLabel>,
    label2: TWire<'a, WordLabel>,
) -> TWire<'a, bool> {
    let mut acc = b.lit(true);
    for (idx, (&v1, &v2)) in label1.repr.iter().zip(label2.repr.iter()).enumerate() {
        let idx = b.lit(idx as u8);
        let check = b.not(in_range(b, idx, offset, width));
        acc = b.and(acc, b.mux(check, b.lit(true), b.eq(v1, v2)));
    }
    acc
}

// Checks if the byte at index idx is in range.
fn in_range<'a>(
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
    calc_regs: &IfMode<AnyTainted, Vec<TWire<'a,WordLabel>>>,
    trace_regs: &IfMode<AnyTainted, Vec<TWire<'a,WordLabel>>>,
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
    init_regs: &IfMode<AnyTainted, Vec<TWire<'a,WordLabel>>>,
) {
    if let Some(init_regs) = init_regs.try_get() {
        for (i, &r) in init_regs.iter().enumerate() {
            wire_assert!(
                cx, b.eq(r, b.lit(WORD_BOTTOM)),
                "initial tainted r{} has value {:?} (expected {:?})",
                i, cx.eval(r), WORD_BOTTOM,
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
        let w = MemOpWidth::W1;
        cx.when(b, b.eq(instr.opcode, b.lit(Opcode::Sink1 as u8)), |cx| {
            let y = convert_to_label(cx, b, idx, calc_im.y);
            let xts = calc_im.tainted.as_ref().unwrap(&pf).label_x;

            // Iterate over labels of xts.
            for (i, &xt) in xts.repr.iter().enumerate() {

                // When the position is relevant, check for sink.
                if i < w.bytes() {

                    // A leak is detected if the label of data being output to a sink does not match the label of
                    // the sink. Equivalent to `not . canFlowTo`.
                    let mt = b.lit(MAYBE_TAINTED);
                    wire_bug_if!(
                        cx, b.and(b.and(b.ne(xt, y), b.ne(xt, b.lit(BOTTOM))), b.and(b.ne(xt, mt), b.ne(y, mt))),
                        "leak of tainted data from register {:x} (byte {}) with label {} does not match output channel label {} on cycle {},{}",
                        cx.eval(instr.op1), i, cx.eval(xt), cx.eval(y), seg_idx, idx,
                    );
                }
            }
        });
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
            let TaintCalcIntermediate{label_x: x_taint, label_y_joined: ty_joined, label_result: _result_taint, addr_offset: offset} = imm.get(&pf);
            let expect_tainted = check_vec(b, *ty_joined, *x_taint);
            let offset = *offset;
            let port_tainted = mem_port.tainted.unwrap(&pf);

            // Shift position by offset.
            let port_shifted = shift_labels(b, port_tainted, offset, BOTTOM);

            let op = mem_port.op;
            let width = mem_port.width;
            // Compare the lowest `width` labels.
            wire_assert!(
                cx, eq_word_labels_with_width(b, mem_port.width, port_shifted, expect_tainted),
                "segment {}: step {}'s mem port (op {:?}, offset {:?}, width {:?}) has tainted {:?} expected {:?} ({:?})",
                seg_idx, idx, cx.eval(op),
                cx.eval(offset), cx.eval(width),
                cx.eval(port_tainted),
                cx.eval(expect_tainted), cx.eval(port_shifted),
            );
        });
    }
}

// Circuit that checks memory when port2 is a read. Since it is a read, port2's tainted must be the same as
// port1's tainted.
pub fn check_read_memports<'a, 'b>(
    cx: &ContextWhen<'a, 'b>,
    b: &Builder<'a>,
    port1label: &TWire<'a, IfMode<AnyTainted,WordLabel>>,
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
    prev_label: &TWire<'a, IfMode<AnyTainted,WordLabel>>,
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
