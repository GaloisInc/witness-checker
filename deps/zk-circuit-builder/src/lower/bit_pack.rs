use crate::gadget::bit_pack::ConcatBits;
use crate::ir::circuit::{
    CircuitTrait, CircuitExt, CircuitRef, CircuitFilter, Wire, TyKind, GateKind,
};

/// Expand any `Bundle` arguments to `ConcatBits`, leaving only `Int` and `Uint`.
pub fn concat_bits_flat<'a>(
    c: &CircuitRef<'a, '_, impl CircuitFilter<'a>>,
    gk: GateKind<'a>,
) -> Wire<'a> {
    if let GateKind::Gadget(g, ws) = gk {
        if let Some(_) = g.cast::<ConcatBits>() {
            if ws.iter().any(|w| !w.ty.is_integer()) {
                let mut new_ws = Vec::new();
                for &w in ws {
                    flatten(c, w, &mut new_ws);
                }
                return c.gadget_iter(g, new_ws);
            }
        }
    }
    c.gate(gk)
}

fn flatten<'a>(c: &impl CircuitTrait<'a>, w: Wire<'a>, out: &mut Vec<Wire<'a>>) {
    match *w.ty {
        TyKind::Bundle(ws) => {
            for i in 0 .. ws.len() {
                flatten(c, c.extract(w, i), out);
            }
        },
        TyKind::Int(_) | TyKind::Uint(_) => { out.push(w); },
        TyKind::GF(f)  => panic!{"ConcatBits is currently unsupported for GF({:?})", f},
    }
}
