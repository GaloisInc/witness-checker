use crate::eval::{self, Evaluator, CachingEvaluator};
use crate::ir::circuit::{self, CircuitTrait, CircuitExt, Wire, GateKind};

pub mod arith;
pub mod bit_pack;


/// For each gadget in the circuit, check that decomposing and then evaluating the gadget produces
/// the same result as evaluating the gadget directly.
pub fn test_gadget_eval<'a, I>(c: &impl CircuitTrait<'a>, wires: I) -> usize
where I: IntoIterator<Item = Wire<'a>> {
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
    let mut tested = 0;
    let mut failed = 0;
    for wire in circuit::walk_wires(wires) {
        let (gk, ws) = match wire.kind {
            GateKind::Gadget(gk, ws) => (gk, ws),
            _ => continue,
        };
        let tys = ws.iter().map(|w| w.ty).collect::<Vec<_>>();
        let xs = ws.iter().map(|&w| ev.eval_wire(c, w)).collect::<Vec<_>>();

        let eval_result = gk.eval(&tys, &xs);
        let decomp_result = ev.eval_wire(c, gk.decompose(c.as_ref(), ws));
        if eval_result != decomp_result {
            eprintln!("error: mismatch in evaluation of {} gate:", gk.name());
            eprintln!("  input types: {:?}", tys);
            eprintln!("  input values: {:?}", xs);
            eprintln!("  eval result: {:?}", eval_result);
            eprintln!("  decompose result: {:?}", decomp_result);
            failed += 1;
        }
        tested += 1;
    }
    if failed > 0 {
        panic!("mismatch in evaluation of {}/{} gadgets", failed, tested);
    }
    tested
}
