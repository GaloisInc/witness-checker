use std::collections::HashMap;
use std::iter;
use crate::ir::circuit::{self, Circuit, Wire, GateKind, Ty, TyKind};

pub mod bool_;
pub mod int;
pub mod bundle;
pub mod gadget;
pub mod const_fold;

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

        let order = circuit::walk_wires_filtered(
            iter::once(old_wire),
            |w| !self.m.contains_key(&w),
        ).collect::<Vec<_>>();

        for old_wire in order {
            let _g = self.c.scoped_label_exact(old_wire.label);

            // Lookups should always succeed, since `order` is supposed to follow the dependency
            // order.
            let get = |w| self.m.get(&w).cloned()
                .unwrap_or_else(|| panic!("missing transformed wire for {:?}", w));

            let old_gate = &*old_wire;
            let new_gate_kind = match old_gate.kind {
                GateKind::Lit(val, ty) => GateKind::Lit(val, self.ty(ty)),
                // TODO: avoid unnecessary duplication of Secrets
                GateKind::Secret(s) => self.c.new_secret(self.ty(s.ty), s.val).kind,
                GateKind::Unary(op, a) => GateKind::Unary(op, get(a)),
                GateKind::Binary(op, a, b) => GateKind::Binary(op, get(a), get(b)),
                GateKind::Shift(op, a, b) => GateKind::Shift(op, get(a), get(b)),
                GateKind::Compare(op, a, b) => GateKind::Compare(op, get(a), get(b)),
                GateKind::Mux(c, t, e) => GateKind::Mux(get(c), get(t), get(e)),
                GateKind::Cast(w, ty) => GateKind::Cast(get(w), self.ty(ty)),
                GateKind::Pack(ws) => self.c.pack_iter(ws.iter().map(|&w| get(w))).kind,
                GateKind::Extract(w, i) => GateKind::Extract(get(w), i),
                GateKind::Gadget(g, ws) => {
                    let g = g.transfer(self.c);
                    self.c.gadget_iter(g, ws.iter().map(|&w| get(w))).kind
                },
            };
            let new_wire = (self.f)(self.c, old_wire, new_gate_kind);
            self.m.insert(old_wire, new_wire);
        }

        self.m.get(&old_wire).cloned()
            .unwrap_or_else(|| panic!("missing transformed wire for {:?} (top level)", old_wire))
    }

    fn ty(&mut self, old_ty: Ty<'old>) -> Ty<'new> {
        if let Some(&new_ty) = self.ty_m.get(&old_ty) {
            return new_ty;
        }

        let new_ty = match *old_ty {
            TyKind::Bool => self.c.ty(TyKind::Bool),
            TyKind::Uint(sz) => self.c.ty(TyKind::Uint(sz)),
            TyKind::Int(sz) => self.c.ty(TyKind::Int(sz)),
            TyKind::Bundle(tys) =>
                self.c.ty_bundle_iter(tys.iter().map(|&ty| self.ty(ty))),
        };
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
