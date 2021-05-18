use crate::ir::circuit::{CircuitTrait, Wire, GateKind, TyKind};

/// Split a `Mux` gate of `Bundle` type into several independent muxes.
pub fn unbundle_mux<'a>(c: &impl CircuitTrait<'a>, gk: GateKind<'a>) -> Wire<'a> {
    /// Unbundle a single mux.  This is recursive so it can handle bundles of bundles.
    fn mk_mux<'a>(
        c: &impl CircuitTrait<'a>,
        cond: Wire<'a>,
        t: Wire<'a>,
        e: Wire<'a>,
    ) -> Wire<'a> {
        let n = match *t.ty {
            TyKind::Bundle(tys) => tys.len(),
            _ => return c.mux(cond, t, e),
        };

        let mut parts = Vec::with_capacity(n);
        for i in 0..n {
            let w = mk_mux(c, cond, c.extract(t, i), c.extract(e, i));
            parts.push(w);
        }
        c.pack(&parts)
    }

    if let GateKind::Mux(cond, t, e) = gk {
        return mk_mux(c, cond, t, e);
    }
    c.gate(gk)
}

/// Simplify away unneeded `Pack` and `Extract` gates.  Specifically, if the input of an `Extract`
/// is a `Pack`, we simply return the appropriate input of the `Pack`, skipping both gates.
///
/// This pass can only remove all bundles if every `Extract` takes a `Pack` as its immediate input.
/// Other passes, such as `unbundle_mux`, can be used to put the circuit into such a form.
pub fn simplify<'a>(c: &impl CircuitTrait<'a>, gk: GateKind<'a>) -> Wire<'a> {
    // This correctly handles nested bundles.  Given `x -> P1 -> P2 -> E2 -> E1`, `simplify`
    // applied to `E2` will collapse `P2 -> E2` and return `P1`, leaving `x -> P1 -> E1`.  Then
    // `simplify` applied to `E1` will collapse `P1 -> E1`, leaving only `x`.
    if let GateKind::Extract(w, i) = gk {
        if let GateKind::Pack(ws) = w.kind {
            return ws[i];
        }
    }
    c.gate(gk)
}
