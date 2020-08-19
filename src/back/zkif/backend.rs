use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};
use crate::back::zkif::representer::{WireId, ZkifId};

use super::gadget_specs::GadgetSpec;

use zkinterface::statement::{StatementBuilder, FileStore};
use zkinterface::{VariablesOwned, CircuitOwned, KeyValueOwned, CommandOwned};
use zkinterface_bellman::sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
use zkinterface_bellman::pairing::bls12_381::Bls12;
use crate::back::zkif::representer::{Representer, En};
use std::path::Path;


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

        let wid = match gate.kind {
            GateKind::Lit(val, ty) => {
                let b = Boolean::constant(val != 0);
                /* TODO: other types.
                match *ty {
                    TyKind::Bool => {}
                };*/

                let wid = self.representer.allocate_repr();
                self.representer.set_bellman_boolean(wid, b);
                wid
            }

            GateKind::Secret(secret) => {
                let val = secret.val.map(|v| v != 0);
                let b = Boolean::from(
                    AllocatedBit::alloc::<En, _>(&mut self.representer, val).unwrap()
                );

                let wid = self.representer.allocate_repr();
                self.representer.set_bellman_boolean(wid, b);
                wid
            }

            GateKind::Unary(op, arg) => {
                let aw = self.wire(arg);
                let ab = self.representer.as_bellman_boolean(aw);

                let out_b = match op {
                    UnOp::Not => ab.not(),
                    UnOp::Neg => ab,
                };

                let wid = self.representer.allocate_repr();
                self.representer.set_bellman_boolean(wid, out_b);
                wid
            }

            GateKind::Binary(op, left, right) => {
                let lw = self.wire(left);
                let rw = self.wire(right);

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

                let wid = self.representer.allocate_repr();
                self.representer.set_bellman_boolean(wid, out_b);
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

