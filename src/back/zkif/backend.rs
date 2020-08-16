use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};
use crate::back::zkif::prototype_backend::{WireRepr, WireId};
use zkinterface::statement::{StatementBuilder, FileStore};

pub struct Backend<'a> {
    gadget_specs: HashMap<String, GadgetSpec>,

    wire_ids: HashMap<Wire<'a>, WireId>,
    wire_representer: WireRepresenter,
}

impl<'a> Backend<'a> {
    pub fn new() -> Backend<'a> {
        let mut b = Backend {
            gadget_specs: HashMap::new(),
            wire_ids: HashMap::new(),
            wire_representer: WireRepresenter::new(),
        };

        b.gadget_specs.insert("cmp".to_owned(), GadgetSpec {
            inputs: vec![
                GadgetConnection { repr_kinds: vec![ReprKind::Packed(1)] },
                GadgetConnection { repr_kinds: vec![ReprKind::Packed(1)] },
            ],
            outputs: vec![
                GadgetConnection { repr_kinds: vec![ReprKind::Bits(1)] },
            ],
        });

        b
    }

    pub fn wire(&mut self, wire: Wire<'a>) -> WireId {
        if let Some(wid) = self.wire_ids.get(&wire) {
            return *wid; // This Wire was already processed.
        }

        let wid = self.wire_representer.allocate_repr();
        self.wire_ids.insert(wire, wid);

        let gate: &Gate = &*wire;
        eprintln!("{:?}", gate);
        match gate.kind {
            GateKind::Compare(op, a, b) => {
                let (a_wid, b_wid) = (self.wire(a), self.wire(b));

                match op {
                    CmpOp::Eq => {
                        let gadget_spec = self.gadget_specs.get("cmp").unwrap();
                        assert_eq!(gadget_spec.inputs.len(), 2);
                        assert_eq!(gadget_spec.outputs.len(), 1);

                        let mut input_vars = Vec::<u64>::new();

                        self.wire_representer.push_zkif_vars(&mut input_vars, a_wid, &gadget_spec.inputs[0]);
                        self.wire_representer.push_zkif_vars(&mut input_vars, b_wid, &gadget_spec.inputs[1]);

                        let result = self.wire_representer.wire_as_field(wid);

                        eprintln!("{:?} := {:?} == {:?}", gate.ty, a.ty, b.ty);
                        eprintln!("{:?} := {:?}", result, input_vars);
                    }
                    _ => unimplemented!("comparison ({:?}) on u64", op),
                }
            }
            _ => {}
        };

        wid
    }




    /*
        if let Some(repr) = self.wire_reprs.get_mut(&wire) {
            return repr;
        }

        let mut repr = ;

        self.wire_reprs.insert(wire, repr);
        self.wire_reprs.get_mut(&wire).unwrap()
     */
}

struct WireRepresenter {
    stmt: StatementBuilder<FileStore>,
    wire_reprs: Vec<WireRepr>,
}

impl WireRepresenter {
    pub fn new() -> WireRepresenter {
        let out_path = "local/test_backend";
        let store = FileStore::new(out_path, true, true, true).unwrap();
        let stmt = StatementBuilder::new(store);

        WireRepresenter { stmt, wire_reprs: vec![] }
    }

    pub fn allocate_repr(&mut self) -> WireId {
        self.wire_reprs.push(WireRepr { packed_zid: None, bit_zids: vec![], one_hot_zids: vec![] });
        WireId(self.wire_reprs.len() - 1)
    }

    fn push_zkif_vars(&mut self, input_vars: &mut Vec<u64>, wid: WireId, gadget_conn: &GadgetConnection) {
        for repr_kind in &gadget_conn.repr_kinds {
            match repr_kind {
                ReprKind::Packed(1) => {
                    let zkid = self.wire_as_field(wid);
                    input_vars.push(zkid);
                }
                ReprKind::Packed(_) => { unimplemented!("large packed input") }
                ReprKind::Bits(_) => { unimplemented!("bits input") }
                ReprKind::OneHot(_) => { unimplemented!("one-hot input") }
            }
        }
    }

    pub fn wire_as_field(&mut self, wid: WireId) -> u64 {
        let repr = &mut self.wire_reprs[wid.0];
        match repr.packed_zid {
            Some(zid) => zid,
            None => {
                // Allocate a field variable.
                let zid = self.stmt.vars.allocate();
                repr.packed_zid = Some(zid);
                // TODO: if other representations exists, enforce equality.
                zid
            }
        }
    }
}

struct GadgetSpec {
    inputs: Vec<GadgetConnection>,
    outputs: Vec<GadgetConnection>,
}

struct GadgetConnection {
    repr_kinds: Vec<ReprKind>
}

enum ReprKind {
    Packed(usize),
    Bits(usize),
    OneHot(usize),
}