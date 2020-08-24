use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp, Ty};

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
use crate::back::zkif::representer::{Representer, En, LC, Fr, FrRepr, WireId, ZkifId, Num};
use std::path::Path;
use std::ops::Sub;
use crate::ir::circuit::IntSize::I64;
use crate::back::zkif::num::boolean_lc;


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
                    TyKind::Int(_) => {}
                    TyKind::Uint(_) => {
                        let f = Fr::from_repr(FrRepr::from(val)).unwrap();
                        let lc = LC::zero() + (f, Representer::one());
                        let num = Num { value: Some(f), lc };
                        self.representer.set_bellman_num(wid, num);
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
                        let value = secret.val.map(|val|
                            Fr::from_repr(FrRepr::from(val)).unwrap());

                        let var = self.representer.alloc(
                            || "secret",
                            || value.ok_or(SynthesisError::AssignmentMissing),
                        ).unwrap();

                        let lc = LC::zero() + var;
                        let num = Num { value, lc };
                        self.representer.set_bellman_num(wid, num);
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
                        let num = self.representer.as_bellman_num(aw);
                        let out_num = match op {
                            UnOp::Neg | UnOp::Not => {
                                Num::zero() - &num
                            }
                            // TODO: NOT should be bitwise negation.
                        };
                        self.representer.set_bellman_num(wid, out_num);
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
                        let left = self.representer.as_bellman_num(lw);
                        let right = self.representer.as_bellman_num(rw);

                        let out_num = match op {
                            BinOp::Add => {
                                left + &right
                            }
                            BinOp::Sub => {
                                left - &right
                            }
                            BinOp::Mul => {
                                left.mul(&right, &mut self.representer)
                            }
                            _ => left, // TODO
                        };

                        self.representer.set_bellman_num(wid, out_num);
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
                //eprintln!("{:?} {:?} {:?}", op, left.ty, right.ty);

                let lw = self.wire(left);
                let rw = self.wire(right);
                let wid = self.representer.allocate_repr();

                let yes = match op {
                    CmpOp::Eq => {
                        let ln = self.representer.as_bellman_num(lw);
                        let rn = self.representer.as_bellman_num(rw);

                        let diff = ln - &rn;

                        let equal_value = diff.value.map(|d| d.is_zero());
                        let equal = Boolean::from(
                            AllocatedBit::alloc::<En, _>(&mut self.representer, equal_value).unwrap()
                        );
                        //let eq_lc = boolean_lc(&equal, Representer::one(), Fr::one());
                        let ne = equal.not();
                        let ne_lc = boolean_lc(&ne, Representer::one(), Fr::one());

                        eprintln!("{} {} {:?}", equal_value.unwrap(), ne.get_value().unwrap(), diff.value.unwrap());

                        self.representer.enforce(
                            || "ne=0 => diff=0",
                            |lc| lc + &diff.lc,
                            |lc| lc + &ne_lc,
                            |lc| lc + &diff.lc,
                        );
                        /*
                        self.representer.enforce(
                            || "diff=0 => ne=0",
                            |lc| lc + &diff.lc,
                            |lc| lc + &ne_lc,
                            |lc| lc + &ne_lc,
                        );
                         */

                        // TODO: should be doable in two constraints instead of three.
                        equal
                    }
                    _ => Boolean::constant(false)
                };

                self.representer.set_bellman_boolean(wid, yes);
                wid
            }

            GateKind::Mux(cond, then_, else_) => {
                unimplemented!("mux");
            }

            GateKind::Cast(a, ty) => {
                //eprintln!("CAST {:?} to {:?}", a.ty, ty);
                let aw = self.wire(a);

                match (*a.ty, *ty) {
                    (TyKind::Bool, TyKind::Uint(_)) => {
                        // TODO: move to the as_* methods.
                        let bool = self.representer.as_bellman_boolean(aw);
                        let num = Num::from_boolean(&bool, &mut self.representer);
                        self.representer.set_bellman_num(aw, num);
                        aw
                    }

                    (TyKind::Uint(_), TyKind::Bool) => {
                        unimplemented!("Cannot cast integer to boolean");
                    }

                    _ => aw
                }
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

