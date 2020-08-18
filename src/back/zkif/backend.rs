use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};
use crate::back::zkif::representer::{WireId, ZkifId};

use super::gadget_specs::GadgetSpec;

use zkinterface::statement::{StatementBuilder, FileStore};
use zkinterface::{VariablesOwned, CircuitOwned, KeyValueOwned, CommandOwned};
use zkinterface_libsnark::gadgetlib::call_gadget_cb;
use zkinterface_bellman::sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
use zkinterface_bellman::pairing::bls12_381::Bls12;
use crate::back::zkif::representer::{WireRepresenter, En};

pub struct Backend<'a> {
    gadget_specs: HashMap<String, GadgetSpec>,

    wire_ids: HashMap<Wire<'a>, WireId>,
    wire_representer: WireRepresenter,
}

impl<'a> Backend<'a> {
    pub fn new() -> Backend<'a> {
        Backend {
            gadget_specs: GadgetSpec::make_specs(),
            wire_ids: HashMap::new(),
            wire_representer: WireRepresenter::new(),
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
                let b = Boolean::constant(val != 0);

                let wid = self.wire_representer.allocate_repr();
                self.wire_representer.set_bellman_boolean(wid, b);

                /* TODO: other types.
                match *ty {
                    TyKind::Bool => {}
                };*/
                eprintln!("{} = Literal boolean", wid.0);
                wid
            }

            GateKind::Secret(secret) => {
                let val = secret.val.map(|v| v != 0);
                let b = Boolean::from(
                    AllocatedBit::alloc::<En, _>(&mut self.wire_representer, val).unwrap()
                );

                let wid = self.wire_representer.allocate_repr();
                self.wire_representer.set_bellman_boolean(wid, b);

                /* TODO: other types.
                match *ty {
                    TyKind::Bool => {}
                };*/
                eprintln!("{} = Secret boolean", wid.0);
                wid
            }

            GateKind::Unary(op, arg) => {
                let aw = self.wire(arg);
                let ab = self.wire_representer.as_bellman_boolean(aw);

                let out_b = ab.not();

                let wid = self.wire_representer.allocate_repr();
                self.wire_representer.set_bellman_boolean(wid, out_b);

                /* TODO: other types and ops.
                match *arg.ty
                match op
                 */
                eprintln!("{} = {:?} {}", wid.0, op, aw.0);
                wid
            }

            GateKind::Binary(op, left, right) => {
                let lw = self.wire(left);
                let rw = self.wire(right);

                let lb = self.wire_representer.as_bellman_boolean(lw);
                let rb = self.wire_representer.as_bellman_boolean(rw);

                let out_b = Boolean::xor::<En, _>(
                    &mut self.wire_representer,
                    &lb, &rb,
                ).unwrap();

                let wid = self.wire_representer.allocate_repr();
                self.wire_representer.set_bellman_boolean(wid, out_b);

                eprintln!("{} = {} {:?} {}", wid.0, lw.0, op, rw.0);
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

            GateKind::Mux(a, b, c) => {
                self.wire(a);
                self.wire(b);
                self.wire(c)
            }

            GateKind::Cast(a, _) => {
                self.wire(a)
            }

            GateKind::Pack(wires) => {
                for w in wires {
                    self.wire(*w);
                }
                self.wire(wires[0])
            }

            GateKind::Extract(a, _) => {
                self.wire(a)
            }

            GateKind::Gadget(gk, wires) => {
                for w in wires {
                    self.wire(*w);
                }
                self.wire(wires[0])
            }
        };

        self.wire_ids.insert(wire, wid);
        wid
    }
}

