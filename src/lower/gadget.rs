use crate::ir::circuit::{
    CircuitBase, CircuitFilter, CircuitRef, DynCircuitRef, Wire, GateKind, GadgetKindRef,
};
use crate::ir::migrate::{self, Migrate};


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
    F1: Fn(GadgetKindRef<'a>) -> bool + 'static,
    F2: CircuitFilter<'a> + 'a,
    F2: Migrate<'a, 'a, Output = F2>,
{
    circuit_filter_common_methods!();

    fn gate(&self, base: &CircuitBase<'a>, gk: GateKind<'a>) -> Wire<'a> {
        if let GateKind::Gadget(k, ws) = gk {
            if (self.filter)(k) {
                // Filter with `self`, not `self.1`, so any newly produced gadgets will be
                // decomposed recursively.
                let c: DynCircuitRef = CircuitRef { base, filter: self };
                return k.decompose(c, ws);
            }
        }
        self.rest.gate(base, gk)
    }
}

impl<'a, 'b, F1, F2> Migrate<'a, 'b> for DecomposeGadgets<F1, F2>
where
    F1: 'static,
    F2: Migrate<'a, 'b>,
{
    type Output = DecomposeGadgets<F1, F2::Output>;
    fn migrate<V: migrate::Visitor<'a, 'b> + ?Sized>(self, v: &mut V) -> Self::Output {
        DecomposeGadgets {
            filter: self.filter,
            rest: v.visit(self.rest),
        }
    }
}
