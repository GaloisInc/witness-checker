#![cfg(feature = "sieve_ir")]

use scuttlebutt::field::{FiniteField, SmallBinaryField, Gf40, Gf45, F56b, F63b, F64b};
use zk_circuit_builder::eval::{self, CachingEvaluator, Evaluator};
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitFilter, DynCircuit, FilterNil, TyKind, Wire,
};
use zk_circuit_builder::ir::typed::{self, Builder};
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

    // TODO
    // // Convert to zkif and validate
    // let dir = tempfile::tempdir().unwrap();
    //
    // let sink = FilesSink::new_clean(&dir.path()).unwrap();
    // let ir_builder = IRBuilder::new::<Scalar>(sink);
    // let mut backend = Backend::new(ir_builder);
    // backend.enforce_true(w);
    // let ir_builder = backend.finish();
    // ir_builder.finish();

    // TODO: Validate the circuit and witness.
    // let mut reader = Reader::new();
    // for f in &files {
    //     reader.read_file(f).unwrap();
    // }
    // validate::<Scalar>(&reader, false).unwrap();
    //
    // dir.close().unwrap();
}

fn inverse<F>(x:F)
where
    F:FiniteField,
    F:for<'a> typed::Eq<'a, Output = bool>,
    F:for<'a> typed::Lit<'a>,
    F:for<'a> typed::Mul<'a, Output = F>,
    F:for<'a> typed::Repr<'a, Repr = Wire<'a>>,
{
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    let b = Builder::new(&c);


    let inv = b.lit(x.inverse());
    let x = b.lit(x);
    let w = b.eq(b.mul(x, inv), b.lit(F::ONE));

    finish(&c, *w);
}

#[test]
fn inverse_f40b() {
    let x = Gf40::from_lower_bits(1234);
    inverse(x)
}

#[test]
fn inverse_f45b() {
    let x = Gf45::from_lower_bits(1234);
    inverse(x)
}

#[test]
fn inverse_f56b() {
    let x = F56b::from_lower_bits(1234);
    inverse(x)
}

#[test]
fn inverse_f63b() {
    let x = F63b::from_lower_bits(1234);
    inverse(x)
}

#[test]
fn inverse_f64b() {
    let x = F64b::from(1234 as u64);
    inverse(x)
}

