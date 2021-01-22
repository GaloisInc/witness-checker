use std::collections::HashMap;
use std::iter;
use crate::eval::{self, Evaluator, CachingEvaluator};
use crate::ir::circuit::{self, Circuit, Wire, GateKind, Ty, TyKind};

pub mod bit_pack;
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
                GateKind::Lit(val, ty) => {
                    let new_ty = self.ty(ty);
                    let new_val = self.c.bits(new_ty, val);
                    GateKind::Lit(new_val, new_ty)
                },
                // TODO: avoid unnecessary duplication of Secrets
                GateKind::Secret(s) => self.c.new_secret_init(self.ty(s.ty), s.val()).kind,
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

/// Run a transformation pass, with extra checks to detect if a pass changes the behavior of the
/// circuit.
pub fn run_pass_debug<'new>(
    c: &Circuit<'new>,
    wire: Vec<Wire>,
    mut f: impl FnMut(&Circuit<'new>, Wire, GateKind<'new>) -> Wire<'new>,
) -> Vec<Wire<'new>> {
    let arena = bumpalo::Bump::new();
    let old_c = Circuit::new(&arena, c.is_prover());
    let wire = run_pass(&old_c, wire, |c, _, gk| c.gate(gk));
    let mut old_ev = CachingEvaluator::<eval::RevealSecrets>::new(&old_c);
    let mut new_ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);
    run_pass(c, wire, |c, old, gk| {
        let old_val = old_ev.eval_wire(old);
        let new = f(c, old, gk);
        let new_val = new_ev.eval_wire(new);
        if old.ty.transfer(c) == new.ty && old_val != new_val {
            let old_g = crate::debug::graphviz::make_graph(&old_c, vec![old].into_iter()).unwrap();
            let new_g = crate::debug::graphviz::make_graph(&c, vec![new].into_iter()).unwrap();
            std::fs::write("pass_debug_old.dot", old_g).unwrap();
            std::fs::write("pass_debug_new.dot", new_g).unwrap();
            panic!(
                "pass changed gate value:\n\
                \x20 old gate: {:?}\n\
                \x20 new gate: {:?}\n\
                \x20 old value: {:?}\n\
                \x20 new value: {:?}\n",
                old, new, old_val, new_val,
            );
        }
        new
    })
}
