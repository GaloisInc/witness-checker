use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp, Ty, Circuit, IntSize::I32};

//use super::gadget_specs::GadgetSpec;

use zkinterface::statement::{StatementBuilder, FileStore};
use zkinterface::{VariablesOwned, CircuitOwned, KeyValueOwned, CommandOwned};
use zkinterface_bellman::sapling_crypto::circuit::{
    boolean::{AllocatedBit, Boolean},
};
use zkinterface_bellman::ff::{Field, PrimeField};
use zkinterface_bellman::pairing::bls12_381::Bls12;
use zkinterface_bellman::bellman::{ConstraintSystem, SynthesisError};
use crate::back::zkif::zkif_cs::{ZkifCS, En, LC, Fr, FrRepr, Num, fr_from_unsigned};
use std::path::Path;
use std::ops::Sub;
use crate::back::zkif::zkif_cs::fr_from_signed;
use crate::back::zkif::int;
use crate::back::zkif::uint32::UInt32;
use crate::back::zkif::bit_width::BitWidth;
use crate::back::zkif::representer::{Representer, ReprId, WireRepr};


/// zkInterface backend based on Bellman.
///
/// - Walk through gates.
/// - Allocate and retrieve representations of wires.
/// - Write files.
pub struct Backend<'a> {
    wire_to_repr: HashMap<Wire<'a>, ReprId>,
    representer: Representer,
    cs: ZkifCS,

    //gadget_specs: HashMap<String, GadgetSpec>,
}

impl<'a> Backend<'a> {
    pub fn new(workspace: impl AsRef<Path>, proving: bool) -> Backend<'a> {
        Backend {
            //gadget_specs: GadgetSpec::make_specs(),
            wire_to_repr: HashMap::new(),
            representer: Representer::new(),
            cs: ZkifCS::new(workspace, proving),
        }
    }

    pub fn wire(&mut self, wire: Wire<'a>) -> ReprId {
        if let Some(wid) = self.wire_to_repr.get(&wire) {
            return *wid; // This Wire was already processed.
        }

        let wid = self.make_repr(wire);

        self.wire_to_repr.insert(wire, wid);
        wid
    }

    fn make_repr(&mut self, wire: Wire<'a>) -> ReprId {
        // Most gates create a representation for a new wire,
        // but some no-op gates return directly the ReprId of their argument.

        let repr = match wire.kind {
            GateKind::Lit(val, ty) => {
                match *ty {
                    TyKind::Bool => {
                        let b = Boolean::constant(val != 0);
                        WireRepr::from(b)
                    }

                    TyKind::Uint(_) => {
                        let num = Num::from(val);
                        WireRepr::from(num)
                    }

                    TyKind::Int(_) => {
                        let num = Num::from(val as i64);
                        WireRepr::from(num)
                    }

                    _ => unimplemented!("Literal {:?}", ty),
                }
            }

            GateKind::Secret(secret) => {
                match *secret.ty {
                    TyKind::Bool => {
                        let val = secret.val.map(|v| v != 0);
                        let b = Boolean::from(
                            AllocatedBit::alloc::<En, _>(&mut self.cs, val).unwrap()
                        );
                        WireRepr::from(b)
                    }

                    TyKind::U32 | TyKind::I32 => {
                        let value = secret.val.map(|val| val as u32);
                        let int = UInt32::alloc(&mut self.cs, value).unwrap();
                        WireRepr::from(int)
                    }

                    _ => unimplemented!("Secret {:?}", secret.ty),
                }
            }

            GateKind::Unary(op, arg) => {
                let aw = self.wire(arg);

                match *wire.ty {
                    TyKind::Bool => {
                        match op {
                            UnOp::Neg => return aw, // No op, no new wire.

                            UnOp::Not => {
                                let ab = self.representer.mut_repr(aw).as_boolean();
                                WireRepr::from(ab.not())
                            }
                        }
                    }

                    TyKind::I32 | TyKind::U32 => {
                        match op {
                            UnOp::Neg => {
                                let num = self.representer.mut_repr(aw).as_num();
                                let neg = Num::zero() - &num;
                                WireRepr::from(neg)
                            }

                            UnOp::Not => {
                                let int = self.representer.mut_repr(aw).as_uint32(&mut self.cs);
                                let not_bits: Vec<Boolean> = int.bits.iter().map(|bit|
                                    bit.not()
                                ).collect();
                                let not = UInt32::from_bits(&not_bits);
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
                    TyKind::Bool => {
                        let lb = self.representer.mut_repr(lw).as_boolean();
                        let rb = self.representer.mut_repr(rw).as_boolean();

                        let out_bool = match op {
                            BinOp::Xor | BinOp::Add | BinOp::Sub =>
                                Boolean::xor::<En, _>(
                                    &mut self.cs,
                                    &lb, &rb,
                                ).unwrap(),

                            BinOp::And | BinOp::Mul => Boolean::and::<En, _>(
                                &mut self.cs,
                                &lb, &rb,
                            ).unwrap(),

                            BinOp::Or => Boolean::and::<En, _>(
                                &mut self.cs,
                                &lb.not(), &rb.not(),
                            ).unwrap().not(),

                            BinOp::Div | BinOp::Mod => // TODO: validate rb=1?
                                unimplemented!("{:?} for {:?}", op, wire.ty),
                        };

                        WireRepr::from(out_bool)
                    }

                    TyKind::Int(_) | TyKind::Uint(_) => {
                        match op {
                            // Arithmetic ops work on number representations.
                            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                                let left = self.representer.mut_repr(lw).as_num();
                                let right = self.representer.mut_repr(rw).as_num();

                                let out_num = match op {
                                    BinOp::Add => left + &right,

                                    BinOp::Sub => left - &right,

                                    BinOp::Mul =>
                                        left.mul(&right, &mut self.cs),

                                    _ => unreachable!(),
                                };

                                WireRepr::from(out_num)
                            }

                            // Ops using both number and bits representations.
                            BinOp::Div | BinOp::Mod => {
                                let numer_num = self.representer.mut_repr(lw).as_num();
                                let numer_int = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                                let denom_num = self.representer.mut_repr(rw).as_num();
                                let denom_int = self.representer.mut_repr(rw).as_uint32(&mut self.cs);

                                let (quot_num, quot_int, rest_num, rest_int) = int::div(
                                    &mut self.cs,
                                    &numer_num, &numer_int,
                                    &denom_num, &denom_int,
                                );

                                let (out_num, out_int) = match op {
                                    BinOp::Div => (quot_num, quot_int),
                                    BinOp::Mod => (rest_num, rest_int),
                                    _ => unreachable!(),
                                };

                                // TODO? Could cache out_num into the repr.
                                WireRepr::from(out_int)
                            }

                            // Bitwise ops work on bit decompositions.
                            BinOp::Xor | BinOp::And | BinOp::Or => {
                                let lu = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                                let ru = self.representer.mut_repr(rw).as_uint32(&mut self.cs);

                                let out_int = match op {
                                    BinOp::Xor =>
                                        int::bitwise_xor(&mut self.cs, &lu, &ru),

                                    BinOp::And =>
                                        int::bitwise_and(&mut self.cs, &lu, &ru),

                                    BinOp::Or =>
                                        int::bitwise_or(&mut self.cs, &lu, &ru),

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
                match *left.ty {
                    TyKind::I32 | TyKind::U32 => {}
                    _ => unimplemented!("Shift for {:?}", left.ty),
                };

                let amount = {
                    let amount = as_lit(right).unwrap_or_else(|| {
                        panic!("only shifts by literals (not {:?}) are supported", right);
                    }) as i64;
                    match op {
                        ShiftOp::Shl => -amount,
                        ShiftOp::Shr => amount,
                    }
                };

                let lw = self.wire(left);
                let lu = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                let shifted = lu.shr(amount as usize);

                WireRepr::from(shifted)
            }

            GateKind::Compare(op, left, right) => {
                let lw = self.wire(left);

                assert!(
                    as_lit(right) == Some(0),
                    "only comparisons to zero (not {:?}) are supported", right,
                );

                let yes = match op {
                    CmpOp::Eq => {
                        let left = self.representer.mut_repr(lw).as_num();
                        left.equals_zero(&mut self.cs)
                    }

                    CmpOp::Ge => {
                        let int = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                        int.is_positive_or_zero()
                    }

                    _ => unimplemented!("CMP {:?} {:?}", op, left.ty),
                };

                WireRepr::from(yes)
            }

            GateKind::Mux(cond, then_, else_) =>
                unimplemented!("mux"),

            GateKind::Cast(a, ty) => {
                let aw = self.wire(a);

                match (*a.ty, *ty) {
                    (x, y) if x == y =>
                        return aw, // No op, no new wire.

                    (TyKind::Bool, TyKind::Uint(_)) =>
                        return aw, // No op, no new wire.

                    (TyKind::Uint(_), TyKind::Bool) =>
                        panic!("Illegal cast of integer to boolean (use explicit i!=0)"),

                    _ => unimplemented!("Cannot cast {:?} to {:?}", a.ty, ty),
                }
            }

            GateKind::Pack(_wires) =>
                unimplemented!("PACK"),

            GateKind::Extract(a, _index) =>
                unimplemented!("EXTRACT {:?}", a.ty),

            GateKind::Gadget(gk, _wires) =>
                unimplemented!("GADGET {:?}", gk),
        };

        self.representer.new_repr(repr)
    }
}

fn as_lit(wire: Wire) -> Option<u64> {
    match wire.kind {
        GateKind::Lit(x, _) => Some(x),
        _ => None,
    }
}
