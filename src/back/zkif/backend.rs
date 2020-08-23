use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};

use super::gadget_specs::GadgetSpec;

use zkinterface::statement::{StatementBuilder, FileStore};
use zkinterface::{VariablesOwned, CircuitOwned, KeyValueOwned, CommandOwned};
use zkinterface_bellman::sapling_crypto::circuit::{
    boolean::{AllocatedBit, Boolean},
    uint32::UInt32,
};
use zkinterface_bellman::ff::{Field, PrimeField};
use zkinterface_bellman::pairing::bls12_381::Bls12;
use zkinterface_bellman::bellman::{ConstraintSystem};
use crate::back::zkif::representer::{Representer, En, LC, Fr, FrRepr, WireId, ZkifId};
use std::path::Path;
use std::ops::Sub;


/// zkInterface backend based on Bellman.
///
/// - Walk through gates.
/// - Allocate and retrieve representations of wires.
/// - Write files.
pub struct Backend<'a> {
    gadget_specs: HashMap<String, GadgetSpec>,

    wire_ids: HashMap<Wire<'a>, WireId>,
    representer: Representer,
}

impl<'a> Backend<'a> {
    pub fn new(workspace: impl AsRef<Path>, proving: bool) -> Backend<'a> {
        Backend {
            gadget_specs: GadgetSpec::make_specs(),
            wire_ids: HashMap::new(),
            representer: Representer::new(workspace, proving),
        }
    }

    pub fn wire(&mut self, wire: Wire<'a>) -> WireId {
        if let Some(wid) = self.wire_ids.get(&wire) {
            return *wid; // This Wire was already processed.
        }

        let gate: &Gate = &*wire;
        eprintln!("{:?}", gate);

        let wid = match gate.kind {
            GateKind::Lit(val, ty) => {
                let wid = self.representer.allocate_repr();

                match *ty {
                    TyKind::Bool => {
                        let b = Boolean::constant(val != 0);
                        self.representer.set_bellman_boolean(wid, b);
                    }
                    TyKind::Int(_) => {}
                    TyKind::Uint(_) => {
                        let v = Fr::from_repr(FrRepr::from(val)).unwrap();
                        let lc = LC::zero() + (v, Representer::one());
                        self.representer.set_bellman_lc(wid, lc);
                    }
                    TyKind::Bundle(_) => {}
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
                    TyKind::Int(_) => {}
                    TyKind::Uint(_) => {
                        let var = self.representer.alloc(
                            || "secret",
                            || Ok(
                                Fr::from_repr(FrRepr::from(
                                    secret.val.unwrap())
                                ).unwrap()),
                        ).unwrap();
                        let lc = LC::zero() + var;
                        self.representer.set_bellman_lc(wid, lc);
                    }
                    TyKind::Bundle(_) => {}
                };
                wid
            }

            GateKind::Unary(op, arg) => {
                let aw = self.wire(arg);
                let wid = self.representer.allocate_repr();

                match *gate.ty {
                    TyKind::Bool => {
                        let ab = self.representer.as_bellman_boolean(aw);
                        let out_b = match op {
                            UnOp::Not => ab.not(),
                            UnOp::Neg => ab,
                        };
                        self.representer.set_bellman_boolean(wid, out_b);
                    }
                    TyKind::Int(_) => {}
                    TyKind::Uint(_) => {
                        let lc = self.representer.as_bellman_lc(aw);
                        let out_n = match op {
                            UnOp::Neg => LC::zero() - &lc,
                            UnOp::Not => lc, // TODO: what is not integer?
                        };
                        self.representer.set_bellman_lc(wid, out_n);
                    }
                    TyKind::Bundle(_) => {}
                };
                wid
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

                            BinOp::Div | BinOp::Mod => lb, // TODO: validate rb=1?
                        };

                        self.representer.set_bellman_boolean(wid, out_b);
                    }
                    TyKind::Int(_) => {}
                    TyKind::Uint(_) => {
                        let left = self.representer.as_bellman_lc(lw);
                        let right = self.representer.as_bellman_lc(rw);

                        let out_lc = match op {
                            BinOp::Add => left + &right,
                            BinOp::Sub => left - &right,
                            BinOp::Mul => {
                                let product = self.representer.alloc(
                                    || "product",
                                    || Ok(Fr::zero()),
                                ).unwrap();
                                let product_lc = LC::zero() + product;

                                self.representer.enforce(
                                    || "multiplication",
                                    // TODO: calculate product and change to `left`
                                    |_| LC::zero(),
                                    |_| right,
                                    |_| product_lc.clone(),
                                );

                                product_lc
                            }
                            _ => left, // TODO
                        };

                        self.representer.set_bellman_lc(wid, out_lc);
                    }
                    TyKind::Bundle(_) => {}
                }

                wid
            }

            GateKind::Shift(op, left, right) => {
                self.wire(left);
                self.wire(right)
            }

            GateKind::Compare(op, left, right) => {
                self.wire(left);
                self.wire(right)
            }

            GateKind::Mux(cond, then_, else_) => {
                self.wire(cond);
                self.wire(then_);
                self.wire(else_)
            }

            GateKind::Cast(a, _ty) => {
                self.wire(a)
            }

            GateKind::Pack(wires) => {
                for w in wires {
                    self.wire(*w);
                }
                assert_ne!(wires.len(), 0);
                self.wire(wires[0])
            }

            GateKind::Extract(a, _index) => {
                self.wire(a)
            }

            GateKind::Gadget(_gk, wires) => {
                for w in wires {
                    self.wire(*w);
                }
                assert_ne!(wires.len(), 0);
                self.wire(wires[0])
            }
        };

        self.wire_ids.insert(wire, wid);
        wid
    }
}

