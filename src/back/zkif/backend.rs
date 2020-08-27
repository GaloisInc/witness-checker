use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp, Ty, Circuit, IntSize::I32};

//use super::gadget_specs::GadgetSpec;

use zkinterface::statement::{StatementBuilder, FileStore};
use zkinterface::{VariablesOwned, CircuitOwned, KeyValueOwned, CommandOwned};
use zkinterface_bellman::sapling_crypto::circuit::{
    boolean::{AllocatedBit, Boolean},
    uint32::UInt32,
};
use zkinterface_bellman::ff::{Field, PrimeField};
use zkinterface_bellman::pairing::bls12_381::Bls12;
use zkinterface_bellman::bellman::{ConstraintSystem, SynthesisError};
use crate::back::zkif::representer::{Representer, En, LC, Fr, FrRepr, WireId, Num, fr_from_unsigned};
use std::path::Path;
use std::ops::Sub;
use crate::back::zkif::representer::fr_from_signed;
use crate::back::zkif::int;
use crate::back::zkif::bit_width::BitWidth;


/// zkInterface backend based on Bellman.
///
/// - Walk through gates.
/// - Allocate and retrieve representations of wires.
/// - Write files.
pub struct Backend<'a> {
    //gadget_specs: HashMap<String, GadgetSpec>,

    wire_ids: HashMap<Wire<'a>, WireId>,
    representer: Representer,
}

impl<'a> Backend<'a> {
    pub fn new(workspace: impl AsRef<Path>, proving: bool) -> Backend<'a> {
        Backend {
            //gadget_specs: GadgetSpec::make_specs(),
            wire_ids: HashMap::new(),
            representer: Representer::new(workspace, proving),
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
                        self.representer.set_bellman_boolean(wid, b);
                    }

                    TyKind::Uint(_) | TyKind::Int(_) => {
                        let f = match *ty {
                            TyKind::Int(_) => fr_from_signed(val as i64),
                            _ => fr_from_unsigned(val),
                        };
                        let num = Num {
                            value: Some(f),
                            lc: LC::zero() + (f.clone(), Representer::one()),
                            bit_width: BitWidth::Max(64), // It is a literal.
                        };
                        self.representer.set_bellman_num(wid, num);
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
                            AllocatedBit::alloc::<En, _>(&mut self.representer, val).unwrap()
                        );
                        self.representer.set_bellman_boolean(wid, b);
                    }

                    TyKind::Uint(I32) | TyKind::Int(I32) => {
                        let value = secret.val.map(|val| {
                            match *secret.ty {
                                TyKind::Int(_) => fr_from_signed(val as i64),
                                _ => fr_from_unsigned(val),
                            }
                        });

                        let var = self.representer.alloc(
                            || "secret",
                            || value.ok_or(SynthesisError::AssignmentMissing),
                        ).unwrap();

                        let num = Num {
                            value,
                            lc: LC::zero() + var,
                            bit_width: BitWidth::Max(32), // Proven below.
                        };
                        self.representer.set_bellman_num(wid, num);

                        // Validate size as a side-effect.
                        let _ = self.representer.as_bellman_uint32(wid);
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
                                let ab = self.representer.as_bellman_boolean(aw);
                                let wid = self.representer.allocate_repr();
                                self.representer.set_bellman_boolean(wid, ab.not());
                                wid
                            }

                            UnOp::Neg => aw, // No op.
                        }
                    }

                    TyKind::Int(I32) | TyKind::Uint(I32) => {
                        let wid = self.representer.allocate_repr();

                        match op {
                            UnOp::Neg => {
                                let num = self.representer.as_bellman_num(aw);
                                let neg = Num::zero() - &num;
                                self.representer.set_bellman_num(wid, neg);
                            }

                            UnOp::Not => {
                                let int = self.representer.as_bellman_uint32(aw);
                                let bits = int.into_bits();
                                let negs: Vec<Boolean> = bits.iter().map(|bit|
                                    bit.not()
                                ).collect();
                                let not = UInt32::from_bits(&negs);
                                self.representer.set_bellman_uint32(wid, not);
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
                        let lb = self.representer.as_bellman_boolean(lw);
                        let rb = self.representer.as_bellman_boolean(rw);

                        let out_b = match op {
                            BinOp::Xor | BinOp::Add | BinOp::Sub =>
                                Boolean::xor::<En, _>(
                                    &mut self.representer,
                                    &lb, &rb,
                                ).unwrap(),

                            BinOp::And | BinOp::Mul => Boolean::and::<En, _>(
                                &mut self.representer,
                                &lb, &rb,
                            ).unwrap(),

                            BinOp::Or => Boolean::and::<En, _>(
                                &mut self.representer,
                                &lb.not(), &rb.not(),
                            ).unwrap().not(),

                            BinOp::Div | BinOp::Mod => // TODO: validate rb=1?
                                unimplemented!("{:?} for {:?}", op, gate.ty),
                        };

                        self.representer.set_bellman_boolean(wid, out_b);
                    }

                    TyKind::Int(_) | TyKind::Uint(_) => {
                        match op {
                            // Arithmetic ops work on number representations.
                            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                                let left = self.representer.as_bellman_num(lw);
                                let right = self.representer.as_bellman_num(rw);

                                let out_num = match op {
                                    BinOp::Add => left + &right,

                                    BinOp::Sub => left - &right,

                                    BinOp::Mul =>
                                        left.mul(&right, &mut self.representer),

                                    _ => unreachable!(),
                                };

                                self.representer.set_bellman_num(wid, out_num);
                            }

                            // Ops using both number and bits representations.
                            BinOp::Div | BinOp::Mod => {
                                let left_num = self.representer.as_bellman_num(lw);
                                let left_int = self.representer.as_bellman_uint32(lw);
                                let right_num = self.representer.as_bellman_num(rw);
                                let right_int = self.representer.as_bellman_uint32(rw);

                                let (quotient, rest) = int::div(
                                    &mut self.representer,
                                    &left_num, &left_int,
                                    &right_num, &right_int,
                                );

                                let out = match op {
                                    BinOp::Div => quotient,
                                    BinOp::Mod => rest,
                                    _ => unreachable!(),
                                };

                                self.representer.set_bellman_uint32(wid, out);
                            }

                            // Bitwise ops work on bit decompositions.
                            BinOp::Xor | BinOp::And | BinOp::Or => {
                                let lu = self.representer.as_bellman_uint32(lw);
                                let ru = self.representer.as_bellman_uint32(rw);

                                let out = match op {
                                    BinOp::Xor =>
                                        int::bitwise_xor(&mut self.representer, &lu, &ru),

                                    BinOp::And =>
                                        int::bitwise_and(&mut self.representer, &lu, &ru),

                                    BinOp::Or =>
                                        int::bitwise_or(&mut self.representer, &lu, &ru),

                                    _ => unreachable!(),
                                };

                                self.representer.set_bellman_uint32(wid, out);
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
                let lu = self.representer.as_bellman_uint32(lw);

                let shifted = lu.shr(amount as usize);

                let wid = self.representer.allocate_repr();
                self.representer.set_bellman_uint32(wid, shifted);
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
                        let left = self.representer.as_bellman_num(lw);
                        left.equals_zero(&mut self.representer)
                    }

                    CmpOp::Ge => {
                        // Interpret the most significant bit as "is negative".
                        let int = self.representer.as_bellman_uint32(lw);
                        let bits = int.into_bits();
                        bits.last().unwrap().not()
                    }

                    _ => unimplemented!("CMP {:?} {:?}", op, left.ty),
                };

                self.representer.set_bellman_boolean(wid, yes);
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
                        let bool = self.representer.as_bellman_boolean(aw);
                        let num = Num::from_boolean::<Representer>(&bool);
                        self.representer.set_bellman_num(aw, num);
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