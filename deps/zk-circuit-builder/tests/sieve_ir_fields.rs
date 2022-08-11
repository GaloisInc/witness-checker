#![cfg(feature = "sieve_ir")]

use scuttlebutt::field::{FiniteField, F64b};
use zk_circuit_builder::eval::{self, CachingEvaluator, Evaluator};
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitExt, CircuitFilter, DynCircuit, FilterNil, TyKind, Wire,
};
use zk_circuit_builder::ir::typed::{self, Builder, TWire};
use zk_circuit_builder::lower;
use num_bigint::BigInt;
use zki_sieve::FilesSink;

macro_rules! make_circuit {
    ($arenas:expr) => {{
        let cf = FilterNil.add_pass(lower::int::compare_to_greater_or_equal_to_zero);
        let c = Circuit::new($arenas, true, cf);
        c
    }};
}

fn finish<'a, C: CircuitTrait<'a> + ?Sized>(c: &'a C, w: Wire<'a>) {
    use zk_circuit_builder::back::sieve_ir::{
        backend::{Backend, Scalar},
        ir_builder::IRBuilder,
    };

    // Make sure the circuit is valid.
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(c);
    let val = ev.eval_wire(w).ok();
    assert_eq!(val, Some(eval::Value::Single(BigInt::from(1))));

    // Convert to zkif and validate
    let dir = tempfile::tempdir().unwrap();

    let sink = FilesSink::new_clean(&dir.path()).unwrap();
    let ir_builder = IRBuilder::new::<Scalar>(sink);
    let mut backend = Backend::new(ir_builder);
    backend.enforce_true(w);
    let ir_builder = backend.finish();
    ir_builder.finish();

    // TODO: Validate the circuit and witness.
    // let mut reader = Reader::new();
    // for f in &files {
    //     reader.read_file(f).unwrap();
    // }
    // validate::<Scalar>(&reader, false).unwrap();
    //
    // dir.close().unwrap();
}

fn inverse<'a, F>(x:F)
  where
    F:FiniteField,
    F:typed::Eq<'a, Output = bool>,
    F:typed::Lit<'a>,
    F:typed::Mul<'a, Output = F>,
    F:typed::Repr<'a, Repr = Wire<'a>>,
{
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    // let cf = FilterNil.add_pass(lower::int::compare_to_greater_or_equal_to_zero);
    // let c = Circuit::new(&arenas, true, cf);
    // let c = &c as &DynCircuit;
    let b = Builder::new(&c);


    let inv = b.lit(x.inverse());
    let x = b.lit(x);
    // let w = b.eq(x, b.lit(F::ONE));
    let w = b.eq(b.mul(x, inv), b.lit(F::ONE));

    finish(&c, *w);
}

#[test]
fn inverse_f64b() {
    // let arenas = Arenas::new();
    // let c = make_circuit!(&arenas);
    // // let cf = FilterNil.add_pass(lower::int::compare_to_greater_or_equal_to_zero);
    // // let c = Circuit::new(&arenas, true, cf);
    // // let c = &c as &DynCircuit;
    // let b = Builder::new(&c);


    let x = F64b::ZERO;
    inverse(x);
}

