use num_bigint::BigUint;
use num_traits::Zero;
/// # Wire representations
///
/// We use two different representations of wire values: a bitwise representation (`Int`) where a
/// value is a list of booleans, and a packed representation (`Num`) where a value is encoded as a
/// single field element.
///
/// Conversion from bitwise to packed representation always uses an unsigned interpretation of the
/// bits.  For example, the packed representation of the signed integer `-1_i8` is `255` - notably,
/// it is *not* equal to the negation (in the field) of the field element `1`.  Arithmetic on the
/// packed representation must account for this.  For example, we negate the packed 8-bit value `1`
/// by computing `256 - 1`, giving the correct result `255`.
///
/// Converting from packed back to bitwise representation requires knowing how many bits are needed
/// to represent the full range of values that the wire might carry.  Some operations on packed
/// values can increase the range.  For example, negating `0_i8` produces `256 - 0 = 256`, which is
/// 9 bits wide.  However, this wire still logically carries an 8-bit value; only the lower 8 bits
/// are meaningful.  The conversion to bitwise representation thus converts to a 9-bit value
/// (otherwise the conversion could fail for values like `256`), then truncates to 8 bits.
///
/// This implies some values may have multiple equivalent packed representations.  Specifically,
/// these are equivalence classes mod `2^N`.  Field elements `0`, `256`, `512`, etc all represent
/// the bitwise value `0_u8`.  Since `2^N` does not evenly divide the field modulus, the
/// highest-valued field elements are not safe to use.  The `Num` type will automatically truncate
/// if the operation might return a value that is out of range.
use std::collections::HashMap;
use std::{convert::TryFrom, iter};

use crate::gadget::bit_pack::{ConcatBits, ExtractBits};
use crate::ir::circuit::{self, BinOp, CmpOp, GateKind, ShiftOp, TyKind, UnOp, Wire};

use super::ir_builder::IRBuilderT;
use super::{
    boolean::Boolean,
    field::QuarkScalar,
    int::Int,
    int_ops,
    int_ops::bool_or,
    num,
    representer::{ReprId, Representer, WireRepr},
};

// NICE-TO-HAVE: template with trait PrimeField instead of a specific Scalar.
// Alternative on 255 bits: zkinterface_bellman::bls12_381::Scalar
pub type Scalar = QuarkScalar;
pub type Num = num::Num<Scalar>;

/// zkInterface backend based on Bellman.
///
/// - Walk through gates.
/// - Allocate and retrieve representations of wires.
/// - Write files.
pub struct Backend<'w, 'irb, IRB: IRBuilderT> {
    wire_to_repr: HashMap<Wire<'w>, ReprId>,
    representer: Representer,
    usage: HashMap<Wire<'w>, u64>, // tells the number of times a given wire is used as an input.
    optim: bool,
    builder: &'irb mut IRB,
}

impl<'w, 'irb, IRB: IRBuilderT> Backend<'w, 'irb, IRB> {
    /// Must call finish() to finalize the files in the workspace.
    pub fn new(ir_builder: &'irb mut IRB) -> Self {
        Backend {
            wire_to_repr: HashMap::new(),
            representer: Representer::new(),
            usage: HashMap::new(),
            optim: true,
            builder: ir_builder,
        }
    }

    pub fn finish(self) {}

    pub fn enforce_true(&mut self, wire: Wire<'w>) {
        let repr_id = self.represent(wire);
        let bool = self.representer.mut_repr(repr_id).as_boolean(self.builder);
        bool.enforce_true(self.builder).unwrap();
    }

    fn get_num(&mut self, repr_id: ReprId) -> Num {
        self.representer.mut_repr(repr_id).as_num(self.builder)
    }

    fn get_num_trunc(&mut self, repr_id: ReprId, width: impl Into<usize>) -> Num {
        self.representer
            .mut_repr(repr_id)
            .as_num_trunc(self.builder, width.into())
    }

    fn get_int(&mut self, repr_id: ReprId, width: impl Into<usize>) -> Int {
        self.representer
            .mut_repr(repr_id)
            .as_int(self.builder, width.into())
    }

    fn get_boolean(&mut self, repr_id: ReprId) -> Boolean {
        self.representer.mut_repr(repr_id).as_boolean(self.builder)
    }

    fn represent(&mut self, wire: Wire<'w>) -> ReprId {
        if let Some(wid) = self.wire_to_repr.get(&wire) {
            if let Some(wire_usage) = self.usage.get_mut(&wire) {
                *wire_usage -= 1;
            }
            return *wid; // This Wire was already processed.
        }

        let order =
            circuit::walk_wires_filtered(iter::once(wire), |w| !self.wire_to_repr.contains_key(&w))
                .collect::<Vec<_>>();

        for wire in order.iter() {
            for dependency in circuit::wire_deps(*wire) {
                if let Some(wire_usage) = self.usage.get_mut(&dependency) {
                    *wire_usage += 1;
                } else {
                    self.usage.insert(dependency, 1);
                }
            }
        }

        for wire in order {
            self.builder
                .annotate(&format!("{}", wire.kind.variant_name()));

            let wid = self.make_repr(wire);
            self.wire_to_repr.insert(wire, wid);

            self.builder.deannotate();
        }

        self.wire_to_repr.get(&wire).cloned().unwrap()
    }

    fn forget_wire_if_required(&mut self, wire: &Wire<'w>, repr: ReprId) {
        if self.optim && self.usage.get(&wire) == Some(&0) {
            self.representer.mut_repr(repr).deallocate();
        }
    }

    fn make_repr(&mut self, wire: Wire<'w>) -> ReprId {
        // Most gates create a representation for a new wire,
        // but some no-op gates return directly the ReprId of their argument.

        let repr = match wire.kind {
            GateKind::Lit(val, ty) => match *ty {
                TyKind::Uint(sz) | TyKind::Int(sz) => {
                    let num = Num::from_biguint(self.builder, sz.bits(), &val.to_biguint());
                    WireRepr::from(num)
                }

                _ => unimplemented!("Literal {:?}", ty),
            },
            GateKind::Secret(secret) => {
                match *secret.ty {
                    TyKind::Uint(sz) | TyKind::Int(sz) => {
                        // TODO: can we use Num::alloc here instead?
                        let int = Int::alloc(
                            self.builder,
                            sz.bits() as usize,
                            secret.val().map(|val| val.to_biguint()),
                        );
                        WireRepr::from(int)
                    }

                    _ => unimplemented!("Secret {:?}", secret.ty),
                }
            }

            GateKind::Unary(op, arg) => {
                let aw = self.represent(arg);

                match *wire.ty {
                    TyKind::BOOL => {
                        match op {
                            UnOp::Neg => return aw, // No op, no new wire.

                            UnOp::Not => {
                                let ab = self.get_boolean(aw);
                                self.forget_wire_if_required(&arg, aw);
                                WireRepr::from(ab.not())
                            }
                        }
                    }

                    TyKind::Uint(sz) | TyKind::Int(sz) => {
                        match op {
                            UnOp::Neg => {
                                let num = self.get_num(aw);
                                let out_num = num
                                    .neg(self.builder)
                                    .or_else(|_| {
                                        let num = self.get_num_trunc(aw, sz.bits());
                                        num.neg(self.builder)
                                    })
                                    .unwrap_or_else(|e| panic!("failed to {:?}: {}", op, e));
                                self.forget_wire_if_required(&arg, aw);
                                WireRepr::from(out_num)
                            }

                            UnOp::Not => {
                                // TODO: could compute this as `-num - 1`
                                let int = self.get_int(aw, sz.bits());
                                let not_bits: Vec<Boolean> =
                                    int.bits.iter().map(|bit| bit.not()).collect();
                                let not = Int::from_bits(&not_bits);
                                self.forget_wire_if_required(&arg, aw);
                                WireRepr::from(not)
                            }
                        }
                    }

                    _ => unimplemented!("Unary {:?} {:?}", op, arg.ty),
                }
            }

            GateKind::Binary(op, left, right) => {
                let lw = self.represent(left);
                let rw = self.represent(right);

                match *wire.ty {
                    TyKind::BOOL => {
                        let lb = self.get_boolean(lw);
                        let rb = self.get_boolean(rw);

                        let out_bool = match op {
                            BinOp::Xor | BinOp::Add | BinOp::Sub => {
                                Boolean::xor(self.builder, &lb, &rb)
                            }

                            BinOp::And | BinOp::Mul => Boolean::and(self.builder, &lb, &rb),

                            BinOp::Or => bool_or(self.builder, &lb, &rb),

                            BinOp::Div | BinOp::Mod => unimplemented!("{:?} for {:?}", op, wire.ty),
                        };
                        self.forget_wire_if_required(&left, lw);
                        self.forget_wire_if_required(&right, rw);
                        WireRepr::from(out_bool)
                    }

                    TyKind::Int(sz) | TyKind::Uint(sz) => {
                        match op {
                            // Arithmetic ops work on number representations.
                            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                                let left_num = self.get_num(lw);
                                let right_num = self.get_num(rw);

                                let do_bin_op = |l: Num, r: Num, b: &mut IRB| match op {
                                    BinOp::Add => l.add_assign(&r, b),
                                    BinOp::Sub => l.sub(&r, b),
                                    BinOp::Mul => l.mul(&r, b),
                                    _ => unreachable!(),
                                };

                                // The operation might fail if the `real_bits` of `left` and
                                // `right` are too big.  In that case, use `as_num_trunc` to reduce
                                // the `real_bits` as much as possible, then try again.
                                let out_num = do_bin_op(left_num, right_num, self.builder)
                                    .or_else(|_| {
                                        let left = self.get_num_trunc(lw, sz.bits());
                                        let right = self.get_num_trunc(rw, sz.bits());
                                        do_bin_op(left, right, self.builder)
                                    })
                                    .unwrap_or_else(|e| panic!("failed to {:?}: {}", op, e));
                                self.forget_wire_if_required(&left, lw);
                                self.forget_wire_if_required(&right, rw);
                                WireRepr::from(out_num)
                            }

                            // Ops using both number and bits representations.
                            BinOp::Div | BinOp::Mod => {
                                if wire.ty.is_int() {
                                    // NICE-TO-HAVE: implement signed division
                                    unimplemented!("signed division");
                                }

                                // Needs truncated `Num`s, with no bogus high bits that could
                                // affect the result.
                                let numer_num = self.get_num_trunc(lw, sz.bits());
                                let numer_int = self.get_int(lw, sz.bits());
                                let denom_num = self.get_num_trunc(rw, sz.bits());
                                let denom_int = self.get_int(rw, sz.bits());

                                let (quot_num, quot_int, rest_num, rest_int) = int_ops::div(
                                    self.builder,
                                    &numer_num,
                                    &numer_int,
                                    &denom_num,
                                    &denom_int,
                                );

                                let (out_num, out_int) = match op {
                                    BinOp::Div => (quot_num, quot_int),
                                    BinOp::Mod => (rest_num, rest_int),
                                    _ => unreachable!(),
                                };

                                self.forget_wire_if_required(&left, lw);
                                self.forget_wire_if_required(&right, rw);
                                // Save both Num and Int representations since we have them.
                                WireRepr::from((out_num, out_int))
                            }

                            // Bitwise ops work on bit decompositions.
                            BinOp::Xor | BinOp::And | BinOp::Or => {
                                let lu = self.get_int(lw, sz.bits());
                                let ru = self.get_int(rw, sz.bits());

                                let out_int = match op {
                                    BinOp::Xor => int_ops::bitwise_xor(self.builder, &lu, &ru),

                                    BinOp::And => int_ops::bitwise_and(self.builder, &lu, &ru),

                                    BinOp::Or => int_ops::bitwise_or(self.builder, &lu, &ru),

                                    _ => unreachable!(),
                                };
                                self.forget_wire_if_required(&left, lw);
                                self.forget_wire_if_required(&right, rw);
                                WireRepr::from(out_int)
                            }
                        }
                    }

                    _ => unimplemented!("Binary {:?} on {:?}", op, wire.ty),
                }
            }

            GateKind::Shift(op, left, right) => {
                let width = match *left.ty {
                    TyKind::Uint(sz) | TyKind::Int(sz) => sz.bits() as usize,
                    _ => panic!("don't know how to shift {:?}", left.ty),
                };

                let amount = as_lit(right).unwrap_or_else(|| {
                    panic!("only shifts by literals are supported (not {:?})", right);
                });
                let amount = usize::try_from(amount).unwrap_or_else(|_| {
                    panic!("shift amount {:?} out of range", right);
                });

                let lw = self.represent(left);
                let lu = self.get_int(lw, width);
                let shifted = match op {
                    ShiftOp::Shl => lu.shift_left(amount),
                    ShiftOp::Shr => lu.shift_right(amount, left.ty.is_int()),
                };
                WireRepr::from(shifted)
            }

            GateKind::Compare(op, left, right) => {
                let lw = self.represent(left);
                let width = left.ty.integer_size().bits() as usize;

                assert!(
                    as_lit(right).map_or(false, |val| val.is_zero()),
                    "only comparisons to zero are supported (not {:?})",
                    right,
                );

                let yes = match op {
                    CmpOp::Eq => {
                        // Needs a truncated `Num`, with no bogus high bits.
                        let left = self.get_num_trunc(lw, width);
                        left.equals_zero(self.builder)
                    }

                    CmpOp::Ge => {
                        let int = self.get_int(lw, width);
                        int.is_positive_or_zero()
                    }

                    _ => unimplemented!("CMP {:?} {:?}", op, left.ty),
                };
                self.forget_wire_if_required(&left, lw);
                WireRepr::from(yes)
            }

            GateKind::Mux(cond, then_, else_) => {
                let cw = self.represent(cond);
                let tw = self.represent(then_);
                let ew = self.represent(else_);
                let cond_num = self.get_num_trunc(cw, 1 as usize);
                let then_num = self.get_num(tw);
                let else_num = self.get_num(ew);
                let out_num = then_num.mux(&else_num, &cond_num, self.builder).unwrap_or_else(|e| {
                    panic!("failed to mux: {}", e);
                });
                self.forget_wire_if_required(&then_, tw);
                self.forget_wire_if_required(&else_, ew);
                self.forget_wire_if_required(&cond, cw);
                WireRepr::from(out_num)
            }

            GateKind::Cast(a, ty) => {
                let aw = self.represent(a);
                let width = a.ty.integer_size().bits() as usize;
                let int = self.get_int(aw, width);

                match (*a.ty, *ty) {
                    (TyKind::Int(sz1), TyKind::Uint(sz2)) if sz1 == sz2 => return aw,
                    (TyKind::Uint(sz1), TyKind::Int(sz2)) if sz1 == sz2 => return aw,

                    (TyKind::Uint(_sz1), TyKind::Uint(sz2))
                    | (TyKind::Uint(_sz1), TyKind::Int(sz2)) => {
                        let mut bits = int.bits.clone();
                        bits.resize(sz2.bits() as usize, Boolean::constant(false));
                        WireRepr::from(Int::from_bits(&bits))
                    }

                    (TyKind::Int(_sz1), TyKind::Uint(sz2))
                    | (TyKind::Int(_sz1), TyKind::Int(sz2)) => {
                        let mut bits = int.bits.clone();
                        let last = bits.last().unwrap().clone();
                        bits.resize(sz2.bits() as usize, last);
                        WireRepr::from(Int::from_bits(&bits))
                    }

                    _ => unimplemented!("Cannot cast {:?} to {:?}", a.ty, ty),
                }
            }

            GateKind::Pack(_wires) => unimplemented!("PACK"),

            GateKind::Extract(a, _index) => unimplemented!("EXTRACT {:?}", a.ty),

            GateKind::Gadget(gk, ws) => {
                if let Some(_) = gk.cast::<ConcatBits>() {
                    let mut bits = Vec::new();
                    for &a in ws {
                        let aw = self.represent(a);
                        let width = a.ty.integer_size().bits() as usize;
                        let int = self.get_int(aw, width);
                        bits.extend_from_slice(&int.bits);
                        self.forget_wire_if_required(&a, aw);
                    }
                    WireRepr::from(Int::from_bits(&bits))
                } else if let Some(g) = gk.cast::<ExtractBits>() {
                    assert!(ws.len() == 1);
                    let a = ws[0];
                    let aw = self.represent(a);
                    let width = a.ty.integer_size().bits() as usize;
                    let int = self.get_int(aw, width);
                    let bits = &int.bits[g.start as usize..g.end as usize];
                    self.forget_wire_if_required(&a, aw);
                    WireRepr::from(Int::from_bits(bits))
                } else {
                    unimplemented!("GADGET {}", gk.name());
                }
            }
        };

        self.representer.new_repr(repr)
    }
}

fn as_lit(wire: Wire) -> Option<BigUint> {
    match wire.kind {
        GateKind::Lit(x, _) => Some(x.to_biguint()),
        _ => None,
    }
}

#[test]
fn test_backend_sieve_ir() -> zki_sieve::Result<()> {
    use super::field::_scalar_from_unsigned;
    use super::ir_builder::IRBuilder;
    use crate::ir::circuit::Circuit;
    use zki_sieve::consumers::evaluator::Evaluator;
    use zki_sieve::producers::sink::MemorySink;
    use zki_sieve::Source;

    let mut ir_builder = IRBuilder::new::<Scalar>(MemorySink::default());

    // If you want a stacktrace to debug duplicate gates, set warnings_panic to true.
    ir_builder.enable_profiler();
    ir_builder.prof.as_mut().map(|p| p.warnings_panic = false);

    let mut back = Backend::new(&mut ir_builder);
    back.optim = false;

    let arena = bumpalo::Bump::new();
    let is_prover = true;
    let c = Circuit::new(&arena, is_prover);

    let zero = c.lit(c.ty(TyKind::I64), 0);
    let lit = c.lit(c.ty(TyKind::I64), 11);
    let sec1 = {
        let (wire, handle) = c.new_secret(c.ty(TyKind::I64));
        handle.set(&c, 12);
        wire
    };
    let sec2 = {
        let (wire, handle) = c.new_secret(c.ty(TyKind::I64));
        handle.set(&c, 13);
        wire
    };
    let prod = c.mul(sec1, sec2);
    let is_zero = c.compare(CmpOp::Eq, prod, zero);
    let diff1 = c.sub(prod, lit);
    let is_ge_zero1 = c.compare(CmpOp::Ge, diff1, zero);
    let diff2 = c.sub(lit, prod);
    let is_ge_zero2 = c.compare(CmpOp::Ge, diff2, zero);

    back.represent(is_zero);
    back.represent(is_ge_zero1);
    back.represent(is_ge_zero2);

    fn check_int<'w, 'irb>(b: &Backend<'w, 'irb, impl IRBuilderT>, w: Wire<'w>, expect: u64) {
        let wi = *b.wire_to_repr.get(&w).unwrap();
        let wr = &b.representer.wire_reprs[wi.0];
        let int = wr.int.as_ref().unwrap();
        assert_eq!(int.value, Some(BigUint::from(expect)));
    }

    fn check_num<'w, 'irb>(b: &Backend<'w, 'irb, impl IRBuilderT>, w: Wire<'w>, expect: u64) {
        let wi = *b.wire_to_repr.get(&w).unwrap();
        let wr = &b.representer.wire_reprs[wi.0];
        let int = wr.num.as_ref().unwrap();
        let value = int.value.unwrap();
        assert_eq!(Ok(value), _scalar_from_unsigned::<Scalar>(expect as u64));
    }

    check_num(&back, lit, 11);
    check_int(&back, sec1, 12);
    check_int(&back, sec2, 13);
    check_num(&back, prod, 12 * 13);
    check_int(&back, diff1, 12 * 13 - 11);
    check_int(&back, diff2, (11 - 12 * 13) as u64);

    back.finish();
    ir_builder.prof.as_ref().map(|p| p.print_report());
    ir_builder.dedup.as_ref().map(|p| p.print_report());
    let sink = ir_builder.finish();
    let source: Source = sink.into();
    let evaluator = Evaluator::from_messages(source.iter_messages());
    assert_eq!(evaluator.get_violations(), Vec::<String>::new());

    Ok(())
}
