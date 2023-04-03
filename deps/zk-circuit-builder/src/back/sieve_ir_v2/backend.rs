//! # Wire representations
//!
//! We use two different representations of wire values: a bitwise representation (`Int`) where a
//! value is a list of booleans, and a packed representation (`Num`) where a value is encoded as a
//! single field element.
//!
//! Conversion from bitwise to packed representation always uses an unsigned interpretation of the
//! bits.  For example, the packed representation of the signed integer `-1_i8` is `255` - notably,
//! it is *not* equal to the negation (in the field) of the field element `1`.  Arithmetic on the
//! packed representation must account for this.  For example, we negate the packed 8-bit value `1`
//! by computing `256 - 1`, giving the correct result `255`.
//!
//! Converting from packed back to bitwise representation requires knowing how many bits are needed
//! to represent the full range of values that the wire might carry.  Some operations on packed
//! values can increase the range.  For example, negating `0_i8` produces `256 - 0 = 256`, which is
//! 9 bits wide.  However, this wire still logically carries an 8-bit value; only the lower 8 bits
//! are meaningful.  The conversion to bitwise representation thus converts to a 9-bit value
//! (otherwise the conversion could fail for values like `256`), then truncates to 8 bits.
//!
//! This implies some values may have multiple equivalent packed representations.  Specifically,
//! these are equivalence classes mod `2^N`.  Field elements `0`, `256`, `512`, etc all represent
//! the bitwise value `0_u8`.  Since `2^N` does not evenly divide the field modulus, the
//! highest-valued field elements are not safe to use.  The `Num` type will automatically truncate
//! if the operation might return a value that is out of range.
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::mem;
use num_bigint::BigUint;
use num_traits::Zero;

use crate::eval::{Evaluator, CachingEvaluator, RevealSecrets};
use crate::gadget::bit_pack::{ConcatBits, ExtractBits};
use crate::ir::circuit::{
    self, CircuitBase, BinOp, CmpOp, GateKind, ShiftOp, TyKind, UnOp, Wire, EraseVisitor,
    MigrateVisitor,
};
use crate::ir::migrate::Visitor as _;

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
pub struct Backend<'w, IRB: IRBuilderT> {
    wire_to_repr: BTreeMap<Wire<'w>, ReprId>,
    representer: Representer,
    builder: IRB,
    ev: CachingEvaluator<'w, 'static, RevealSecrets>,
}

impl<'w, IRB: IRBuilderT> Backend<'w, IRB> {
    /// Must call finish() to finalize the files in the workspace.
    pub fn new(ir_builder: IRB) -> Self {
        Backend {
            wire_to_repr: BTreeMap::new(),
            representer: Representer::new(),
            builder: ir_builder,
            ev: CachingEvaluator::new(),
        }
    }

    pub fn finish(self) -> IRB {
        self.builder
    }

    pub fn enforce_true(&mut self, c: &CircuitBase<'w>, wire: Wire<'w>) {
        let repr_id = self.convert_wires(c, &[wire])[0];
        let bool = self.representer.mut_repr(repr_id).as_boolean(&mut self.builder);
        bool.enforce_true(&mut self.builder).unwrap();
    }

    /// Convert each wire in `wires` to a low-level representation.  Returns a vector of
    /// `wires.len()` entries, containing the `ReprId` for each element of `wires`.
    fn convert_wires(&mut self, c: &CircuitBase<'w>, wires: &[Wire<'w>]) -> Vec<ReprId> {
        let order = circuit::walk_wires_filtered(
            wires.iter().cloned(),
            |w| !self.wire_to_repr.contains_key(&w),
        ).collect::<Vec<_>>();

        for wire in order {
            self.builder.annotate(&format!("{}", wire.kind.variant_name()));

            let repr_id = self.make_repr(c, wire);
            self.wire_to_repr.insert(wire, repr_id);

            self.builder.deannotate();

            self.builder.free_unused();
        }

        wires.iter().map(|&wire| self.wire_to_repr[&wire]).collect()
    }


    fn get_num(&mut self, repr_id: ReprId) -> Num {
        self.representer.mut_repr(repr_id).as_num(&mut self.builder)
    }

    fn get_num_trunc(&mut self, repr_id: ReprId, width: impl Into<usize>) -> Num {
        self.representer
            .mut_repr(repr_id)
            .as_num_trunc(&mut self.builder, width.into())
    }

    fn get_int(&mut self, repr_id: ReprId, width: impl Into<usize>) -> Int {
        self.representer
            .mut_repr(repr_id)
            .as_int(&mut self.builder, width.into())
    }

    fn get_boolean(&mut self, repr_id: ReprId) -> Boolean {
        self.representer.mut_repr(repr_id).as_boolean(&mut self.builder)
    }

    fn represent(&mut self, wire: Wire<'w>) -> ReprId {
        self.wire_to_repr[&wire]
    }

    fn make_repr(&mut self, c: &CircuitBase<'w>, wire: Wire<'w>) -> ReprId {
        // Most gates create a representation for a new wire,
        // but some no-op gates return directly the ReprId of their argument.

        let repr = match wire.kind {
            GateKind::Lit(val, ty) => match *ty {
                TyKind::Uint(sz) | TyKind::Int(sz) => {
                    let num = Num::from_biguint(&mut self.builder, sz.bits(), &val.to_biguint());
                    WireRepr::from(num)
                }

                _ => unimplemented!("Literal {:?}", ty),
            },
            GateKind::Secret(secret) => {
                match *secret.ty {
                    TyKind::Uint(sz) | TyKind::Int(sz) => {
                        // TODO: can we use Num::alloc here instead?
                        let opt_bits = self.ev.eval_wire_bits(c, wire).ok().map(|(b, _)| b);
                        let int = Int::alloc(
                            &mut self.builder,
                            sz.bits() as usize,
                            opt_bits.map(|val| val.to_biguint()),
                        );
                        WireRepr::from(int)
                    }

                    _ => unimplemented!("Secret {:?}", secret.ty),
                }
            }

            GateKind::Erased(_erased) => unimplemented!("Erased"),

            GateKind::Argument(_, _) => unimplemented!("Argument"),

            GateKind::Unary(op, arg) => {
                let aw = self.represent(arg);

                match *wire.ty {
                    TyKind::BOOL => {
                        match op {
                            UnOp::Neg => return aw, // No op, no new wire.

                            UnOp::Not => {
                                let ab = self.get_boolean(aw);
                                WireRepr::from(ab.not())
                            }
                        }
                    }

                    TyKind::Uint(sz) | TyKind::Int(sz) => {
                        match op {
                            UnOp::Neg => {
                                let num = self.get_num(aw);
                                let out_num = num
                                    .neg(&mut self.builder)
                                    .or_else(|_| {
                                        let num = self.get_num_trunc(aw, sz.bits());
                                        num.neg(&mut self.builder)
                                    })
                                    .unwrap_or_else(|e| panic!("failed to {:?}: {}", op, e));
                                WireRepr::from(out_num)
                            }

                            UnOp::Not => {
                                // TODO: could compute this as `-num - 1`
                                let int = self.get_int(aw, sz.bits());
                                let not_bits: Vec<Boolean> =
                                    int.bits.iter().map(|bit| bit.not()).collect();
                                let not = Int::from_bits(&not_bits);
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
                                Boolean::xor(&mut self.builder, &lb, &rb)
                            }

                            BinOp::And | BinOp::Mul => Boolean::and(&mut self.builder, &lb, &rb),

                            BinOp::Or => bool_or(&mut self.builder, &lb, &rb),

                            BinOp::Div | BinOp::Mod => unimplemented!("{:?} for {:?}", op, wire.ty),
                        };
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
                                let out_num = do_bin_op(left_num, right_num, &mut self.builder)
                                    .or_else(|_| {
                                        let left = self.get_num_trunc(lw, sz.bits());
                                        let right = self.get_num_trunc(rw, sz.bits());
                                        do_bin_op(left, right, &mut self.builder)
                                    })
                                    .unwrap_or_else(|e| panic!("failed to {:?}: {}", op, e));
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
                                    &mut self.builder,
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

                                // Save both Num and Int representations since we have them.
                                WireRepr::from((out_num, out_int))
                            }

                            // Bitwise ops work on bit decompositions.
                            BinOp::Xor | BinOp::And | BinOp::Or => {
                                let lu = self.get_int(lw, sz.bits());
                                let ru = self.get_int(rw, sz.bits());

                                let out_int = match op {
                                    BinOp::Xor => int_ops::bitwise_xor(&mut self.builder, &lu, &ru),

                                    BinOp::And => int_ops::bitwise_and(&mut self.builder, &lu, &ru),

                                    BinOp::Or => int_ops::bitwise_or(&mut self.builder, &lu, &ru),

                                    _ => unreachable!(),
                                };
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
                        left.equals_zero(&mut self.builder)
                    }

                    CmpOp::Ge => {
                        let int = self.get_int(lw, width);
                        int.is_positive_or_zero()
                    }

                    _ => unimplemented!("CMP {:?} {:?}", op, left.ty),
                };
                WireRepr::from(yes)
            }

            GateKind::Mux(cond, then_, else_) => {
                let cw = self.represent(cond);
                let tw = self.represent(then_);
                let ew = self.represent(else_);
                let cond_num = self.get_num_trunc(cw, 1 as usize);
                let then_num = self.get_num(tw);
                let else_num = self.get_num(ew);
                let out_num = then_num.mux(&else_num, &cond_num, &mut self.builder)
                    .unwrap_or_else(|e| panic!("failed to mux: {}", e));
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
                    }
                    WireRepr::from(Int::from_bits(&bits))
                } else if let Some(g) = gk.cast::<ExtractBits>() {
                    assert!(ws.len() == 1);
                    let a = ws[0];
                    let aw = self.represent(a);
                    let width = a.ty.integer_size().bits() as usize;
                    let int = self.get_int(aw, width);
                    let bits = &int.bits[g.start as usize..g.end as usize];
                    WireRepr::from(Int::from_bits(bits))
                } else {
                    unimplemented!("GADGET {}", gk.name());
                }
            }

            GateKind::Call(_, _, _) => unimplemented!("Call"),
        };

        self.representer.new_repr(repr)
    }

    pub fn post_erase(&mut self, v: &mut EraseVisitor<'w, '_>) {
        // Each entry `(old, new)` in `v.erased()` indicates that wire `old` was replaced with the
        // new `Erased` wire `new`.  In each case, we construct (or otherwise obtain) a `ReprId`
        // for `old` and copy it into `wire_to_repr[new]` as well.
        let (old_wires, new_wires): (Vec<_>, Vec<_>) = v.erased().iter().cloned().unzip();
        let old_reprs = self.convert_wires(v.new_circuit(), &old_wires);
        for (old_repr, new_wire) in old_reprs.into_iter().zip(new_wires.into_iter()) {
            assert!(!self.wire_to_repr.contains_key(&new_wire));
            self.wire_to_repr.insert(new_wire, old_repr);
        }
    }

    pub fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w, '_>) {
        use crate::ir::migrate::Visitor as _;

        let mut old_representer = mem::replace(&mut self.representer, Representer::new());
        let old_wire_to_repr = mem::take(&mut self.wire_to_repr);

        for (old_wire, old_repr_id) in old_wire_to_repr {
            let new_wire = match v.visit_wire_weak(old_wire) {
                Some(x) => x,
                None => continue,
            };
            let repr = old_representer.take_repr(old_repr_id);
            let new_repr_id = self.representer.new_repr(repr);
            self.wire_to_repr.insert(new_wire, new_repr_id);
        }
    }
}

fn as_lit(wire: Wire) -> Option<BigUint> {
    match wire.kind {
        GateKind::Lit(x, _) => Some(x.to_biguint()),
        _ => None,
    }
}

#[test]
fn test_backend_sieve_ir_v2() -> zki_sieve_v3::Result<()> {
    use super::field::_scalar_from_unsigned;
    use super::ir_builder::IRBuilder;
    use crate::ir::circuit::{Arenas, CircuitBase, CircuitExt};
    use zki_sieve_v3::consumers::evaluator::{Evaluator, PlaintextBackend};
    use zki_sieve_v3::producers::sink::MemorySink;
    use zki_sieve_v3::Source;

    let mut ir_builder = IRBuilder::new::<Scalar>(MemorySink::default(), None);

    // If you want a stacktrace to debug duplicate gates, set warnings_panic to true.
    ir_builder.enable_profiler();
    ir_builder.prof.as_mut().map(|p| p.warnings_panic = false);

    let mut back = Backend::new(ir_builder);

    let arenas = Arenas::new();
    let is_prover = true;
    let c = CircuitBase::new::<()>(&arenas, is_prover);

    let zero = c.lit(c.ty(TyKind::I64), 0);
    let lit = c.lit(c.ty(TyKind::I64), 11);
    let sec1 = {
        let (wire, handle) = c.new_secret_wire(c.ty(TyKind::I64));
        handle.set(&c, 12);
        wire
    };
    let sec2 = {
        let (wire, handle) = c.new_secret_wire(c.ty(TyKind::I64));
        handle.set(&c, 13);
        wire
    };
    let prod = c.mul(sec1, sec2);
    let is_zero = c.compare(CmpOp::Eq, prod, zero);
    let diff1 = c.sub(prod, lit);
    let is_ge_zero1 = c.compare(CmpOp::Ge, diff1, zero);
    let diff2 = c.sub(lit, prod);
    let is_ge_zero2 = c.compare(CmpOp::Ge, diff2, zero);

    back.convert_wires(&c, &[is_zero, is_ge_zero1, is_ge_zero2]);

    fn check_int<'w>(b: &Backend<'w, impl IRBuilderT>, w: Wire<'w>, expect: u64) {
        let wi = *b.wire_to_repr.get(&w).unwrap();
        let wr = &b.representer.wire_reprs[wi.0];
        let int = wr.int.as_ref().unwrap();
        assert_eq!(int.value, Some(BigUint::from(expect)));
    }

    fn check_num<'w>(b: &Backend<'w, impl IRBuilderT>, w: Wire<'w>, expect: u64) {
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

    let ir_builder = back.finish();
    ir_builder.prof.as_ref().map(|p| p.print_report());
    ir_builder.dedup.as_ref().map(|p| p.print_report());
    let sink = ir_builder.finish();
    let source: Source = sink.into();
    let mut backend = PlaintextBackend::default();
    let evaluator = Evaluator::from_messages(source.iter_messages(), &mut backend);
    assert_eq!(evaluator.get_violations(), Vec::<String>::new());

    Ok(())
}
