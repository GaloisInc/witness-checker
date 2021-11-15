use crate::ir::circuit::{
    CircuitExt, CircuitBase, CircuitFilter, CircuitRef, DynCircuitRef, Wire, GateKind,
    GadgetKindRef,
};


pub struct DecomposeGadgets<F1, F2> {
    filter: F1,
    rest: F2,
}

impl<'a, F1, F2> DecomposeGadgets<F1, F2>
where
    F1: Fn(GadgetKindRef<'a>) -> bool,
    F2: CircuitFilter<'a>,
{
    /// Extend filter `rest` with a `DecomposeGadgets` pass that decomposes any gadget on which
    /// `filter` returns `true`.
    pub fn new(rest: F2, filter: F1) -> DecomposeGadgets<F1, F2> {
        DecomposeGadgets { filter, rest }
    }
}

impl<'a, F1, F2> CircuitFilter<'a> for DecomposeGadgets<F1, F2>
where
    F1: Fn(GadgetKindRef<'a>) -> bool + 'a,
    F2: CircuitFilter<'a> + 'a,
{
    fn as_dyn(&self) -> &(dyn CircuitFilter<'a> + 'a) { self }

    fn gate(&self, base: &CircuitBase<'a>, gk: GateKind<'a>) -> Wire<'a> {
        if let GateKind::Gadget(k, ws) = gk {
            if (self.filter)(k) {
                // Filter with `self`, not `self.1`, so any newly produced gadgets will be
                // decomposed recursively.
                let c: DynCircuitRef = CircuitRef { base, filter: self };
                let _g = c.scoped_label(k.name());
                return k.decompose(c, ws);
            }
        }
        self.rest.gate(base, gk)
    }
}
