use std::collections::HashMap;
use crate::ir::circuit::{Circuit, Wire, GateKind, Ty, TyKind};

pub mod bool_;
pub mod int;

struct RunPass<'a, 'old, 'new, F> {
    c: &'a Circuit<'new>,
    f: F,
    m: HashMap<Wire<'old>, Wire<'new>>,
    ty_m: HashMap<Ty<'old>, Ty<'new>>,
}

impl<'a, 'old, 'new, F> RunPass<'a, 'old, 'new, F>
where F: FnMut(&Circuit<'new>, Wire<'old>, GateKind<'new>) -> Wire<'new> {
    fn new(c: &'a Circuit<'new>, f: F) -> RunPass<'a, 'old, 'new, F> {
        RunPass {
            c, f,
            m: HashMap::new(),
            ty_m: HashMap::new(),
        }
    }

    fn wire(&mut self, old_wire: Wire<'old>) -> Wire<'new> {
        if let Some(&new_wire) = self.m.get(&old_wire) {
            return new_wire;
        }

        let old_gate = &*old_wire;
        let new_gate_kind = match old_gate.kind {
            GateKind::Lit(val, ty) => GateKind::Lit(val, self.ty(ty)),
            // TODO: avoid unnecessary duplication of Secrets
            GateKind::Secret(s) => self.c.new_secret(self.ty(s.ty), s.val).kind,
            GateKind::Unary(op, a) => GateKind::Unary(op, self.wire(a)),
            GateKind::Binary(op, a, b) => GateKind::Binary(op, self.wire(a), self.wire(b)),
            GateKind::Shift(op, a, b) => GateKind::Shift(op, self.wire(a), self.wire(b)),
            GateKind::Compare(op, a, b) => GateKind::Compare(op, self.wire(a), self.wire(b)),
            GateKind::Mux(c, t, e) => GateKind::Mux(self.wire(c), self.wire(t), self.wire(e)),
            GateKind::Cast(w, ty) => GateKind::Cast(self.wire(w), self.ty(ty)),
        };
        let new_wire = (self.f)(self.c, old_wire, new_gate_kind);
        self.m.insert(old_wire, new_wire);
        new_wire
    }

    fn ty(&mut self, old_ty: Ty<'old>) -> Ty<'new> {
        if let Some(&new_ty) = self.ty_m.get(&old_ty) {
            return new_ty;
        }

        let new_ty_kind = match *old_ty {
            TyKind::Bool => TyKind::Bool,
            TyKind::Uint(sz) => TyKind::Uint(sz),
            TyKind::Int(sz) => TyKind::Int(sz),
        };
        let new_ty = self.c.ty(new_ty_kind);
        self.ty_m.insert(old_ty, new_ty);
        new_ty
    }
}

pub fn run_pass<'old, 'new>(
    c: &Circuit<'new>,
    wire: Vec<Wire<'old>>,
    f: impl FnMut(&Circuit<'new>, Wire<'old>, GateKind<'new>) -> Wire<'new>,
) -> Vec<Wire<'new>> {
    let mut rp = RunPass::new(c, f);
    wire.into_iter().map(|w| rp.wire(w)).collect()
}
