#![cfg(feature = "bellman")]

use std::path::Path;
use bumpalo::Bump;
use num_bigint::BigInt;
use cheesecloth::eval::{self, Evaluator, CachingEvaluator};
use cheesecloth::ir::circuit::{Circuit, TyKind, Wire};
use cheesecloth::lower::{self, run_pass};

fn finish<'a>(c: &Circuit<'a>, w: Wire<'a>) {
    use cheesecloth::back::zkif::backend::{Backend, Scalar};
    use std::fs::remove_file;
    use zkinterface::Reader;
    use zkinterface_bellman::zkif_backend::validate;


    let ws = vec![w];
    let ws = run_pass(&c, ws, lower::int::compare_to_greater_or_equal_to_zero);
    let w = ws[0];


    // Make sure the circuit is valid.
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(c);
    let val = ev.eval_wire(w);
    assert_eq!(val, Some(eval::Value::Single(BigInt::from(1))));


    // Convert to zkif and validate
    let dir = tempfile::tempdir().unwrap();

    let workspace = dir.path();
    let files = vec![
        workspace.join("header.zkif"),
        workspace.join("constraints.zkif"),
        workspace.join("witness.zkif"),
    ];
    for f in &files {
        let _ = remove_file(f);
    }

    let mut backend = Backend::new(workspace, true);
    backend.enforce_true(w);
    backend.finish().unwrap();

    // Validate the circuit and witness.
    let mut reader = Reader::new();
    for f in &files {
        reader.read_file(f).unwrap();
    }
    validate::<Scalar>(&reader, false).unwrap();

    dir.close().unwrap();
}

#[test]
fn neg_one() {
    let arena = Bump::new();
    let c = Circuit::new(&arena);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.neg(c.lit(t_i8, 1)),
        c.lit(t_i8, -1),
    );

    finish(&c, w);
}

#[test]
fn not_zero() {
    let arena = Bump::new();
    let c = Circuit::new(&arena);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.not(c.lit(t_i8, 0)),
        c.lit(t_i8, -1),
    );

    finish(&c, w);
}

#[test]
fn neg_one_shr() {
    let arena = Bump::new();
    let c = Circuit::new(&arena);
    let t_i8 = c.ty(TyKind::I8);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.shr(c.lit(t_i8, -1), c.lit(t_u8, 1)),
        c.lit(t_i8, -1),
    );

    finish(&c, w);
}
