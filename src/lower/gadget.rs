use crate::ir::circuit::{Circuit, CircuitTrait, CircuitExt, Wire, GateKind, GadgetKindRef};
use crate::lower;

/// Decompose any gadget for which `f(g)` returns `true`.
pub fn decompose_gadgets<'a>(
    mut f: impl FnMut(GadgetKindRef<'a>) -> bool,
) -> impl FnMut(&Circuit<'a>, Wire, GateKind<'a>) -> Wire<'a> {
    move |c, _old, gk| {
        if let GateKind::Gadget(g, args) = gk {
            if f(g) {
                let _g = c.scoped_label(g.name());
                return g.decompose(c, args);
            }
        }
        c.gate(gk)
    }
}

pub fn decompose_all_gadgets<'a>(c: &Circuit<'a>, _old: Wire, gk: GateKind<'a>) -> Wire<'a> {
    if let GateKind::Gadget(g, args) = gk {
        let _g = c.scoped_label(g.name());
        return g.decompose(c, args);
    }
    c.gate(gk)
}


pub struct DecomposeGadgets<C, F>(pub C, pub F);

impl<'a, C, F> CircuitTrait<'a> for DecomposeGadgets<C, F>
where C: CircuitTrait<'a>, F: Fn(GadgetKindRef<'a>) -> bool {
    type Inner = C;
    fn inner(&self) -> &C { &self.0 }

    fn gate(&self, gk: GateKind<'a>) -> Wire<'a> {
        if let GateKind::Gadget(k, ws) = gk {
            if (self.1)(k) {
                let _g = self.scoped_label(k.name());
                let out_raw = k.decompose(self.as_base(), ws);
                // Transfer into `self`, not `self.inner`, so any newly produced gadgets will be
                // decomposed recursively.
                let out = lower::transfer_partial(self, ws.iter().cloned(), vec![out_raw])[0];
                return out;
            }
        }
        self.inner().gate(gk)
    }
}
