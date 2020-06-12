use std::collections::HashMap;
use crate::ir::circuit::{Circuit, Gate, Wire, GateKind};

pub mod bool_;
pub mod int;

struct RunPass<'a, 'old, 'new, F> {
    c: &'a Circuit<'new>,
    f: F,
    m: HashMap<Wire<'old>, Wire<'new>>,
}

impl<'a, 'old, 'new, F> RunPass<'a, 'old, 'new, F>
where F: FnMut(&Circuit<'new>, Gate<'new>) -> Wire<'new> {
    fn wire(&mut self, old_wire: Wire<'old>) -> Wire<'new> {
        if let Some(&new_wire) = self.m.get(&old_wire) {
            return new_wire;
        }

        let old_gate = &*old_wire;
        let new_gate_kind = match old_gate.kind {
            GateKind::Lit(val) => GateKind::Lit(val),
            GateKind::Input(idx) => GateKind::Input(idx),
            GateKind::Unary(op, a) => GateKind::Unary(op, self.wire(a)),
            GateKind::Binary(op, a, b) => GateKind::Binary(op, self.wire(a), self.wire(b)),
            GateKind::Shift(op, a, b) => GateKind::Shift(op, self.wire(a), self.wire(b)),
            GateKind::Compare(op, a, b) => GateKind::Compare(op, self.wire(a), self.wire(b)),
            GateKind::Mux(c, t, e) => GateKind::Mux(self.wire(c), self.wire(t), self.wire(e)),
            GateKind::Cast(w, ty) => GateKind::Cast(self.wire(w), ty),
        };
        let new_gate = Gate {
            ty: old_gate.ty,
            kind: new_gate_kind,
        };
        let new_wire = (self.f)(self.c, new_gate);
        self.m.insert(old_wire, new_wire);
        new_wire
    }
}

pub fn run_pass<'old, 'new>(
    c: &Circuit<'new>,
    wire: Wire<'old>,
    f: impl FnMut(&Circuit<'new>, Gate<'new>) -> Wire<'new>,
) -> Wire<'new> {
    RunPass { c, f, m: HashMap::new() }.wire(wire)
}
