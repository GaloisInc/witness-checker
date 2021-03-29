#![cfg(feature = "sieve_ir")]

use bumpalo::Bump;
use cheesecloth::eval::{self, CachingEvaluator, Evaluator};
use cheesecloth::ir::circuit::{Circuit, TyKind, Wire};
use cheesecloth::lower::{self, run_pass};
use num_bigint::BigInt;
use zki_sieve::FilesSink;

fn finish<'a>(c: &Circuit<'a>, w: Wire<'a>) {
    use cheesecloth::back::sieve_ir::backend::Backend;
    use std::fs::remove_file;

    let ws = vec![w];
    let ws = run_pass(&c, ws, lower::int::compare_to_greater_or_equal_to_zero);
    let w = ws[0];

    // Make sure the circuit is valid.
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(c);
    let val = ev.eval_wire(w);
    assert_eq!(val, Some(eval::Value::Single(BigInt::from(1))));

    // Convert to zkif and validate
    let dir = tempfile::tempdir().unwrap();

    let sink = FilesSink::new_clean(&dir.path()).unwrap();
    let mut backend = Backend::new(sink, true);
    backend.enforce_true(w);
    backend.finish().unwrap();

    // TODO: Validate the circuit and witness.
    // let mut reader = Reader::new();
    // for f in &files {
    //     reader.read_file(f).unwrap();
    // }
    // validate::<Scalar>(&reader, false).unwrap();
    //
    // dir.close().unwrap();
}

#[test]
fn mux_true() {
    let arena = Bump::new();
    let c = Circuit::new(&arena, true);
    let t_bool = c.ty(TyKind::BOOL);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.mux(c.lit(t_bool, 1), c.lit(t_i8, 10), c.lit(t_i8, 20)),
        c.lit(t_i8, 10),
    );

    finish(&c, w);
}

#[test]
fn mux_false() {
    let arena = Bump::new();
    let c = Circuit::new(&arena, true);
    let t_bool = c.ty(TyKind::BOOL);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.mux(c.lit(t_bool, 0), c.lit(t_i8, 10), c.lit(t_i8, 20)),
        c.lit(t_i8, 20),
    );

    finish(&c, w);
}
