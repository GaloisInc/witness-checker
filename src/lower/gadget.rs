use crate::ir::circuit::{Circuit, Wire, GateKind};

/// Decompose any gadget for which `f(g.name())` returns `true`.
pub fn decompose_gadget<'a>(
    mut f: impl FnMut(&str) -> bool,
) -> impl FnMut(&Circuit<'a>, Wire, GateKind<'a>) -> Wire<'a> {
    move |c, _old, gk| {
        if let GateKind::Gadget(g, args) = gk {
            if f(g.name()) {
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
