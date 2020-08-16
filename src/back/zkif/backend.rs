use std::collections::HashMap;
use crate::ir::circuit::{Wire, Gate, TyKind, GateKind, UnOp, BinOp, ShiftOp, CmpOp};
use crate::back::zkif::prototype_backend::{WireRepr, WireId};
use zkinterface::statement::{StatementBuilder, FileStore};

pub struct Backend<'a> {
    wire_ids: HashMap<Wire<'a>, WireId>,
    wire_reprs: Vec<WireRepr>,
    stmt: StatementBuilder<FileStore>,
}

impl<'a> Backend<'a> {
    pub fn new() -> Backend<'a> {
        let out_path = "local/test_backend";
        let store = FileStore::new(out_path, true, true, true).unwrap();
        let stmt = StatementBuilder::new(store);

        Backend {
            wire_ids: HashMap::new(),
            wire_reprs: vec![],
            stmt,
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

    pub fn wire(&mut self, wire: Wire<'a>) -> WireId {
        if let Some(wid) = self.wire_ids.get(&wire) {
            return *wid; // This Wire was already processed.
        }

        self.wire_reprs.push(WireRepr { packed_zid: None, bit_zids: vec![], one_hot_zids: vec![] });
        let wid = WireId(self.wire_reprs.len() - 1);
        self.wire_ids.insert(wire, wid);

        let gate: &Gate = &*wire;
        eprintln!("{:?}", gate);
        match gate.kind {
            GateKind::Compare(op, a, b) => {
                match op {
                    CmpOp::Eq => {
                        let aid = self.wire(a);
                        let bid = self.wire(b);
                        let af = self.wire_as_field(aid);
                        let bf = self.wire_as_field(bid);
                        let result = self.wire_as_field(wid);
                        eprintln!("{:?} := (af {:?} == bf {:?})", result, af, bf);
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