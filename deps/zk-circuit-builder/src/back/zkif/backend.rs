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
use std::collections::HashMap;
use std::convert::TryFrom;
use std::mem;
use std::path::Path;
use num_bigint::BigUint;
use num_traits::Zero;

use crate::eval::{Evaluator, CachingEvaluator, RevealSecrets};
use crate::gadget::bit_pack::{ConcatBits, ExtractBits};
use crate::ir::circuit::{
    self, CircuitBase, BinOp, CmpOp, GateKind, ShiftOp, TyKind, UnOp, Wire, EraseVisitor,
    MigrateVisitor,
};
use crate::ir::migrate::Visitor as _;

use super::{
    field::QuarkScalar,
    int::Int,
    int_ops,
    int_ops::{bool_or, enforce_true},
    num,
    representer::{ReprId, Representer, WireRepr},
};
use zkinterface::Result;
use zkinterface_bellman::{
    bellman::gadgets::boolean::Boolean,
    zkif_cs::ZkifCS,
};

// TODO: template with trait PrimeField instead of a specific Scalar.
// Alternative on 255 bits: zkinterface_bellman::bls12_381::Scalar
pub type Scalar = QuarkScalar;
pub type Num = num::Num<Scalar>;
pub type CS = ZkifCS<Scalar>;

/// zkInterface backend based on Bellman.
///
/// - Walk through gates.
/// - Allocate and retrieve representations of wires.
/// - Write files.
pub struct Backend<'a> {
    wire_to_repr: HashMap<Wire<'a>, ReprId>,
    representer: Representer,
    cs: ZkifCS<Scalar>,
}

impl<'a> Backend<'a> {
    /// Must call finish() to finalize the files in the workspace.
    pub fn new(workspace: impl AsRef<Path>, proving: bool) -> Backend<'a> {
        Backend {
            wire_to_repr: HashMap::new(),
            representer: Representer::new(),
            cs: ZkifCS::new(workspace, proving),
        }
    }

    pub fn finish(self) -> Result<()> {
        self.cs.finish("cheesecloth")
    }

    pub fn enforce_true(
        &mut self,
        c: &CircuitBase<'a>,
        ev: &mut impl Evaluator<'a>,
        wire: Wire<'a>,
    ) {
        let repr_id = self.convert_wires(c, ev, &[wire])[0];
        let bool = self.representer.mut_repr(repr_id).as_boolean(&mut self.cs);
        enforce_true(&mut self.cs, &bool);
    }

    pub fn get_bool(&mut self, wire: Wire<'a>) -> Option<bool> {
        let repr_id = self.wire(wire);
        let bool = self.representer.mut_repr(repr_id).as_boolean(&mut self.cs);
        bool.get_value()
    }

    fn convert_wires(
        &mut self,
        c: &CircuitBase<'a>,
        ev: &mut impl Evaluator<'a>,
        wires: &[Wire<'a>],
    ) -> Vec<ReprId> {
        let order = circuit::walk_wires_filtered(
            wires.iter().cloned(),
            |w| !self.wire_to_repr.contains_key(&w),
        ).collect::<Vec<_>>();

        for wire in order {
            let wid = self.make_repr(c, ev, wire);
            self.wire_to_repr.insert(wire, wid);
        }

        wires.iter().map(|&wire| self.wire_to_repr[&wire]).collect()
    }

    fn wire(&mut self, wire: Wire<'a>) -> ReprId {
        self.wire_to_repr[&wire]
    }

    fn make_repr(
        &mut self,
        c: &CircuitBase<'a>,
        ev: &mut impl Evaluator<'a>,
        wire: Wire<'a>,
    ) -> ReprId {
        // Most gates create a representation for a new wire,
        // but some no-op gates return directly the ReprId of their argument.

        let repr = match wire.kind {
            GateKind::Lit(val, ty) => match *ty {
                TyKind::Uint(sz) | TyKind::Int(sz) => {
                    let num = Num::from_biguint(sz.bits(), &val.to_biguint());
                    WireRepr::from(num)
                }

                _ => unimplemented!("Literal {:?}", ty),
            },

            GateKind::Secret(secret) => {
                match *secret.ty {
                    TyKind::Uint(sz) | TyKind::Int(sz) => {
                        // TODO: can we use Num::alloc here instead?
                        let opt_bits = ev.eval_wire_bits(c, wire).ok().map(|(b, _)| b);
                        let int = Int::alloc::<Scalar, _>(
                            &mut self.cs,
                            sz.bits() as usize,
                            opt_bits.map(|val| val.to_biguint()),
                        )
                        .unwrap();
                        WireRepr::from(int)
                    }

                    _ => unimplemented!("Secret {:?}", secret.ty),
                }
            }

            GateKind::Erased(_erased) => unimplemented!("Erased"),

            GateKind::Argument(_, _) => unimplemented!("Argument"),

            GateKind::Unary(op, arg) => {
                let aw = self.wire(arg);

                match *wire.ty {
                    TyKind::BOOL => {
                        match op {
                            UnOp::Neg => return aw, // No op, no new wire.

                            UnOp::Not => {
                                let ab = self.representer.mut_repr(aw).as_boolean(&mut self.cs);
                                WireRepr::from(ab.not())
                            }
                        }
                    }

                    TyKind::Uint(sz) | TyKind::Int(sz) => {
                        match op {
                            UnOp::Neg => {
                                let num = self.representer.mut_repr(aw).as_num();
                                let out_num = num
                                    .neg(&mut self.cs)
                                    .or_else(|_| {
                                        let num = self
                                            .representer
                                            .mut_repr(aw)
                                            .as_num_trunc(&mut self.cs);
                                        num.neg(&mut self.cs)
                                    })
                                    .unwrap_or_else(|e| panic!("failed to {:?}: {}", op, e));
                                WireRepr::from(out_num)
                            }

                            UnOp::Not => {
                                // TODO: could compute this as `-num - 1`
                                let int = self
                                    .representer
                                    .mut_repr(aw)
                                    .as_int(&mut self.cs, sz.bits() as usize);
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
                let lw = self.wire(left);
                let rw = self.wire(right);

                match *wire.ty {
                    TyKind::BOOL => {
                        let lb = self.representer.mut_repr(lw).as_boolean(&mut self.cs);
                        let rb = self.representer.mut_repr(rw).as_boolean(&mut self.cs);

                        let out_bool = match op {
                            BinOp::Xor | BinOp::Add | BinOp::Sub => {
                                Boolean::xor(&mut self.cs, &lb, &rb).unwrap()
                            }

                            BinOp::And | BinOp::Mul => {
                                Boolean::and(&mut self.cs, &lb, &rb).unwrap()
                            }

                            BinOp::Or => bool_or(&mut self.cs, &lb, &rb),

                            BinOp::Div | BinOp::Mod => unimplemented!("{:?} for {:?}", op, wire.ty),
                        };

                        WireRepr::from(out_bool)
                    }

                    TyKind::Int(sz) | TyKind::Uint(sz) => {
                        match op {
                            // Arithmetic ops work on number representations.
                            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                                let left = self.representer.mut_repr(lw).as_num();
                                let right = self.representer.mut_repr(rw).as_num();

                                let do_bin_op = |l: Num, r: Num, cs: &mut ZkifCS<Scalar>| match op {
                                    BinOp::Add => l.add(&r, cs),
                                    BinOp::Sub => l.sub(&r, cs),
                                    BinOp::Mul => l.mul(&r, cs),
                                    _ => unreachable!(),
                                };

                                // The operation might fail if the `real_bits` of `left` and
                                // `right` are too big.  In that case, use `as_num_trunc` to reduce
                                // the `real_bits` as much as possible, then try again.
                                let out_num = do_bin_op(left, right, &mut self.cs)
                                    .or_else(|_| {
                                        let left = self
                                            .representer
                                            .mut_repr(lw)
                                            .as_num_trunc(&mut self.cs);
                                        let right = self
                                            .representer
                                            .mut_repr(rw)
                                            .as_num_trunc(&mut self.cs);
                                        do_bin_op(left, right, &mut self.cs)
                                    })
                                    .unwrap_or_else(|e| panic!("failed to {:?}: {}", op, e));

                                WireRepr::from(out_num)
                            }

                            // Ops using both number and bits representations.
                            BinOp::Div | BinOp::Mod => {
                                // FIXME: this is incorrect for signed division
                                // Needs truncated `Num`s, with no bogus high bits that could
                                // affect the result.
                                let numer_num =
                                    self.representer.mut_repr(lw).as_num_trunc(&mut self.cs);
                                let numer_int = self
                                    .representer
                                    .mut_repr(lw)
                                    .as_int(&mut self.cs, sz.bits() as usize);
                                let denom_num =
                                    self.representer.mut_repr(rw).as_num_trunc(&mut self.cs);
                                let denom_int = self
                                    .representer
                                    .mut_repr(rw)
                                    .as_int(&mut self.cs, sz.bits() as usize);

                                let (quot_num, quot_int, rest_num, rest_int) = int_ops::div(
                                    &mut self.cs,
                                    &numer_num,
                                    &numer_int,
                                    &denom_num,
                                    &denom_int,
                                );

                                let (_out_num, out_int) = match op {
                                    BinOp::Div => (quot_num, quot_int),
                                    BinOp::Mod => (rest_num, rest_int),
                                    _ => unreachable!(),
                                };

                                // TODO? Could cache out_num into the repr.
                                WireRepr::from(out_int)
                            }

                            // Bitwise ops work on bit decompositions.
                            BinOp::Xor | BinOp::And | BinOp::Or => {
                                let lu = self
                                    .representer
                                    .mut_repr(lw)
                                    .as_int(&mut self.cs, sz.bits() as usize);
                                let ru = self
                                    .representer
                                    .mut_repr(rw)
                                    .as_int(&mut self.cs, sz.bits() as usize);

                                let out_int = match op {
                                    BinOp::Xor => int_ops::bitwise_xor(&mut self.cs, &lu, &ru),

                                    BinOp::And => int_ops::bitwise_and(&mut self.cs, &lu, &ru),

                                    BinOp::Or => int_ops::bitwise_or(&mut self.cs, &lu, &ru),

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

                let lw = self.wire(left);
                let lu = self.representer.mut_repr(lw).as_int(&mut self.cs, width);
                let shifted = match op {
                    ShiftOp::Shl => lu.shift_left(amount),
                    ShiftOp::Shr => lu.shift_right(amount, left.ty.is_int()),
                };

                WireRepr::from(shifted)
            }

            GateKind::Compare(op, left, right) => {
                let lw = self.wire(left);
                let width = left.ty.integer_size().bits() as usize;

                assert!(
                    as_lit(right).map_or(false, |val| val.is_zero()),
                    "only comparisons to zero are supported (not {:?})",
                    right,
                );

                let yes = match op {
                    CmpOp::Eq => {
                        // Needs a truncated `Num`, with no bogus high bits.
                        let left = self.representer.mut_repr(lw).as_num_trunc(&mut self.cs);
                        left.equals_zero(&mut self.cs)
                    }

                    CmpOp::Ge => {
                        let int = self.representer.mut_repr(lw).as_int(&mut self.cs, width);
                        int.is_positive_or_zero()
                    }

                    _ => unimplemented!("CMP {:?} {:?}", op, left.ty),
                };

                WireRepr::from(yes)
            }

            GateKind::Mux(cond, then_, else_) => {
                let cw = self.wire(cond);
                let tw = self.wire(then_);
                let ew = self.wire(else_);
                let cond = self.representer.mut_repr(cw).as_num_trunc(&mut self.cs);
                let then_ = self.representer.mut_repr(tw).as_num();
                let else_ = self.representer.mut_repr(ew).as_num();
                let out_num = then_.mux(&else_, &cond, &mut self.cs).unwrap_or_else(|e| {
                    panic!("failed to mux: {}", e);
                });
                WireRepr::from(out_num)
            }

            GateKind::Cast(a, ty) => {
                let aw = self.wire(a);
                let width = a.ty.integer_size().bits() as usize;
                let int = self.representer.mut_repr(aw).as_int(&mut self.cs, width);

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
                        let aw = self.wire(a);
                        let width = a.ty.integer_size().bits() as usize;
                        let int = self.representer.mut_repr(aw).as_int(&mut self.cs, width);
                        bits.extend_from_slice(&int.bits);
                    }
                    WireRepr::from(Int::from_bits(&bits))
                } else if let Some(g) = gk.cast::<ExtractBits>() {
                    assert!(ws.len() == 1);
                    let a = ws[0];
                    let aw = self.wire(a);
                    let width = a.ty.integer_size().bits() as usize;
                    let int = self.representer.mut_repr(aw).as_int(&mut self.cs, width);
                    let bits = &int.bits[g.start as usize..g.end as usize];
                    WireRepr::from(Int::from_bits(bits))
                } else {
                    unimplemented!("GADGET {}", gk.name());
                }
            }

            GateKind::Call(_) => unimplemented!("Call"),
        };

        self.representer.new_repr(repr)
    }

    pub fn post_erase(&mut self, v: &mut EraseVisitor<'a, '_>) {
        // Each entry `(old, new)` in `v.erased()` indicates that wire `old` was replaced with the
        // new `Erased` wire `new`.  In each case, we construct (or otherwise obtain) a `ReprId`
        // for `old` and copy it into `wire_to_repr[new]` as well.
        let (old_wires, new_wires): (Vec<_>, Vec<_>) = v.erased().iter()
            .filter(|&&(w, _)| !matches!(*w.ty, TyKind::RawBits))
            .cloned().unzip();
        let old_reprs = self.convert_wires(v.new_circuit(), &mut *v.evaluator(), &old_wires);
        for (old_repr, new_wire) in old_reprs.into_iter().zip(new_wires.into_iter()) {
            assert!(!self.wire_to_repr.contains_key(&new_wire));
            self.wire_to_repr.insert(new_wire, old_repr);
        }
    }

    pub fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a, '_>) {
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
fn test_zkif() -> Result<()> {
    use crate::eval::{self, CachingEvaluator};
    use crate::ir::circuit::{Arenas, CircuitBase, CircuitExt, Ty};
    use super::num::_scalar_from_unsigned;

    let mut b = Backend::new(Path::new("local/test"), true);

    let arenas = Arenas::new();
    let c = CircuitBase::new::<()>(&arenas, true);
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();

    let zero = c.lit(c.ty(TyKind::I64), 0);
    let lit = c.lit(c.ty(TyKind::I64), 11);
    let sec1 = c.secret_immediate(Ty::int(64), 12_i64);
    let sec2 = c.secret_immediate(Ty::int(64), 13_i64);
    let prod = c.mul(sec1, sec2);
    let is_zero = c.compare(CmpOp::Eq, prod, zero);
    let diff1 = c.sub(prod, lit);
    let is_ge_zero1 = c.compare(CmpOp::Ge, diff1, zero);
    let diff2 = c.sub(lit, prod);
    let is_ge_zero2 = c.compare(CmpOp::Ge, diff2, zero);

    b.convert_wires(&c, &mut ev, &[is_zero, is_ge_zero1, is_ge_zero2]);

    fn check_int<'a>(b: &Backend<'a>, w: Wire<'a>, expect: u64) {
        let wi = *b.wire_to_repr.get(&w).unwrap();
        let wr = &b.representer.wire_reprs[wi.0];
        let int = wr.int.as_ref().unwrap();
        assert_eq!(int.value, Some(BigUint::from(expect)));
    }

    fn check_num<'a>(b: &Backend<'a>, w: Wire<'a>, expect: u64) {
        let wi = *b.wire_to_repr.get(&w).unwrap();
        let wr = &b.representer.wire_reprs[wi.0];
        let int = wr.num.as_ref().unwrap();
        let value = int.value.unwrap();
        assert_eq!(Ok(value), _scalar_from_unsigned::<Scalar>(expect as u64));
    }

    check_num(&b, lit, 11);
    check_int(&b, sec1, 12);
    check_int(&b, sec2, 13);
    check_num(&b, prod, 12 * 13);
    check_int(&b, diff1, 12 * 13 - 11);
    check_int(&b, diff2, (11 - 12 * 13) as u64);

    b.finish()
}
