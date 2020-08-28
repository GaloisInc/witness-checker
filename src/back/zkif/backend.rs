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
use crate::back::zkif::representer::{Representer, WireId};


/// zkInterface backend based on Bellman.
///
/// - Walk through gates.
/// - Allocate and retrieve representations of wires.
/// - Write files.
pub struct Backend<'a> {
    wire_ids: HashMap<Wire<'a>, WireId>,
    representer: Representer,
    cs: ZkifCS,

    //gadget_specs: HashMap<String, GadgetSpec>,
}

impl<'a> Backend<'a> {
    pub fn new(workspace: impl AsRef<Path>, proving: bool) -> Backend<'a> {
        Backend {
            //gadget_specs: GadgetSpec::make_specs(),
            wire_ids: HashMap::new(),
            representer: Representer::new(),
            cs: ZkifCS::new(workspace, proving),
        }
    }

    pub fn wire(&mut self, wire: Wire<'a>) -> WireId {
        if let Some(wid) = self.wire_ids.get(&wire) {
            return *wid; // This Wire was already processed.
        }

        let gate: &Gate = &*wire;
        //eprintln!("{:?}", gate);

        let wid = match gate.kind {
            GateKind::Lit(val, ty) => {
                let wid = self.representer.allocate_repr();

                match *ty {
                    TyKind::Bool => {
                        let b = Boolean::constant(val != 0);
                        self.representer.mut_repr(wid).set_boolean(b);
                    }

                    TyKind::Uint(_) => {
                        let num = Num::from(val);
                        self.representer.mut_repr(wid).set_num(num);
                    }

                    TyKind::Int(_) => {
                        let num = Num::from(val as i64);
                        self.representer.mut_repr(wid).set_num(num);
                    }

                    _ => unimplemented!("Literal {:?}", ty),
                };

                wid
            }

            GateKind::Secret(secret) => {
                let wid = self.representer.allocate_repr();

                match *secret.ty {
                    TyKind::Bool => {
                        let val = secret.val.map(|v| v != 0);
                        let b = Boolean::from(
                            AllocatedBit::alloc::<En, _>(&mut self.cs, val).unwrap()
                        );
                        self.representer.mut_repr(wid).set_boolean(b);
                    }

                    TyKind::Uint(I32) | TyKind::Int(I32) => {
                        let value = secret.val.map(|val| val as u32);
                        let int = UInt32::alloc(&mut self.cs, value).unwrap();
                        self.representer.mut_repr(wid).set_uint32(int);

                        /* Version without size validation:

                        let value = secret.val.map(|val| {
                            match *secret.ty {
                                TyKind::Int(_) => fr_from_signed(val as i64),
                                _ => fr_from_unsigned(val),
                            }
                        });

                        let var = self.cs.alloc(
                            || "secret",
                            || value.ok_or(SynthesisError::AssignmentMissing),
                        ).unwrap();

                        let num = Num {
                            value,
                            lc: LC::zero() + var,
                            bit_width: BitWidth::Unknown,
                        };
                        self.representer.set_bellman_num(wid, num);
                        */
                    }

                    _ => unimplemented!("Secret {:?}", secret.ty),
                };
                wid
            }

            GateKind::Unary(op, arg) => {
                let aw = self.wire(arg);

                match *gate.ty {
                    TyKind::Bool => {
                        match op {
                            UnOp::Not => {
                                let ab = self.representer.mut_repr(aw).as_boolean();
                                let wid = self.representer.allocate_repr();
                                self.representer.mut_repr(wid).set_boolean(ab.not());
                                wid
                            }

                            UnOp::Neg => aw, // No op.
                        }
                    }

                    TyKind::Int(I32) | TyKind::Uint(I32) => {
                        let wid = self.representer.allocate_repr();

                        match op {
                            UnOp::Neg => {
                                let num = self.representer.mut_repr(aw).as_num(&mut self.cs);
                                let neg = Num::zero() - &num;
                                self.representer.mut_repr(wid).set_num(neg);
                            }

                            UnOp::Not => {
                                let int = self.representer.mut_repr(aw).as_uint32(&mut self.cs);
                                let negs: Vec<Boolean> = int.bits.iter().map(|bit|
                                    bit.not()
                                ).collect();
                                let not = UInt32::from_bits(&negs);
                                self.representer.mut_repr(wid).set_uint32(not);
                            }
                        }

                        wid
                    }

                    _ => unimplemented!("Unary {:?} {:?}", op, arg.ty),
                }
            }

            GateKind::Binary(op, left, right) => {
                let lw = self.wire(left);
                let rw = self.wire(right);
                let wid = self.representer.allocate_repr();

                match *gate.ty {
                    TyKind::Bool => {
                        let lb = self.representer.mut_repr(lw).as_boolean();
                        let rb = self.representer.mut_repr(rw).as_boolean();

                        let out_b = match op {
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
                                unimplemented!("{:?} for {:?}", op, gate.ty),
                        };

                        self.representer.mut_repr(wid).set_boolean(out_b);
                    }

                    TyKind::Int(_) | TyKind::Uint(_) => {
                        match op {
                            // Arithmetic ops work on number representations.
                            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                                let left = self.representer.mut_repr(lw).as_num(&mut self.cs);
                                let right = self.representer.mut_repr(rw).as_num(&mut self.cs);

                                let out_num = match op {
                                    BinOp::Add => left + &right,

                                    BinOp::Sub => left - &right,

                                    BinOp::Mul =>
                                        left.mul(&right, &mut self.cs),

                                    _ => unreachable!(),
                                };

                                self.representer.mut_repr(wid).set_num(out_num);
                            }

                            // Ops using both number and bits representations.
                            BinOp::Div | BinOp::Mod => {
                                let numer_num = self.representer.mut_repr(lw).as_num(&mut self.cs);
                                let numer_int = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                                let denom_num = self.representer.mut_repr(rw).as_num(&mut self.cs);
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

                                self.representer.mut_repr(wid).set_num(out_num);
                                self.representer.mut_repr(wid).set_uint32(out_int);
                            }

                            // Bitwise ops work on bit decompositions.
                            BinOp::Xor | BinOp::And | BinOp::Or => {
                                let lu = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                                let ru = self.representer.mut_repr(rw).as_uint32(&mut self.cs);

                                let out = match op {
                                    BinOp::Xor =>
                                        int::bitwise_xor(&mut self.cs, &lu, &ru),

                                    BinOp::And =>
                                        int::bitwise_and(&mut self.cs, &lu, &ru),

                                    BinOp::Or =>
                                        int::bitwise_or(&mut self.cs, &lu, &ru),

                                    _ => unreachable!(),
                                };

                                self.representer.mut_repr(wid).set_uint32(out);
                            }
                        }
                    }

                    _ => unimplemented!("Binary {:?} on {:?}", op, gate.ty),
                }

                wid
            }

            GateKind::Shift(op, left, right) => {
                match *left.ty {
                    TyKind::Int(I32) | TyKind::Uint(I32) => {}
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

                let wid = self.representer.allocate_repr();
                self.representer.mut_repr(wid).set_uint32(shifted);
                wid
            }

            GateKind::Compare(op, left, right) => {
                let lw = self.wire(left);
                let wid = self.representer.allocate_repr();

                assert!(
                    as_lit(right) == Some(0),
                    "only comparisons to zero (not {:?}) are supported", right,
                );

                let yes = match op {
                    CmpOp::Eq => {
                        let left = self.representer.mut_repr(lw).as_num(&mut self.cs);
                        left.equals_zero(&mut self.cs)
                    }

                    CmpOp::Ge => {
                        let int = self.representer.mut_repr(lw).as_uint32(&mut self.cs);
                        int.is_positive()
                    }

                    _ => unimplemented!("CMP {:?} {:?}", op, left.ty),
                };

                self.representer.mut_repr(wid).set_boolean(yes);
                wid
            }

            GateKind::Mux(cond, then_, else_) =>
                unimplemented!("mux"),

            GateKind::Cast(a, ty) => {
                //eprintln!("CAST {:?} to {:?}", a.ty, ty);
                let aw = self.wire(a);

                match (*a.ty, *ty) {
                    (TyKind::Bool, TyKind::Uint(_)) => {
                        // TODO: move to the as_* methods.
                        let bool = self.representer.mut_repr(aw).as_boolean();
                        let num = Num::from_boolean::<ZkifCS>(&bool);
                        self.representer.mut_repr(aw).set_num(num);
                        aw
                    }

                    (TyKind::Uint(_), TyKind::Bool) =>
                        panic!("Illegal cast of integer to boolean (use explicit i!=0)"),

                    (x, y) => {
                        if x == y {
                            aw // No op.
                        } else {
                            unimplemented!("Cannot cast {:?} to {:?}", a.ty, ty);
                        }
                    }
                }
            }

            GateKind::Pack(_wires) =>
                unimplemented!("PACK"),

            GateKind::Extract(a, _index) =>
                unimplemented!("EXTRACT {:?}", a.ty),

            GateKind::Gadget(gk, _wires) =>
                unimplemented!("GADGET {:?}", gk),
        };

        self.wire_ids.insert(wire, wid);
        wid
    }
}

fn as_lit(wire: Wire) -> Option<u64> {
    match wire.kind {
        GateKind::Lit(x, _) => Some(x),
        _ => None,
    }
}