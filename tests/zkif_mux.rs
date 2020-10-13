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
    //let workspace = Path::new("out/test");
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
fn mux_true() {
    let arena = Bump::new();
    let c = Circuit::new(&arena);
    let t_bool = c.ty(TyKind::BOOL);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.mux(
            c.lit(t_bool, 1),
            c.lit(t_i8, 10),
            c.lit(t_i8, 20),
        ),
        c.lit(t_i8, 10),
    );

    finish(&c, w);
}

#[test]
fn mux_false() {
    let arena = Bump::new();
    let c = Circuit::new(&arena);
    let t_bool = c.ty(TyKind::BOOL);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.mux(
            c.lit(t_bool, 0),
            c.lit(t_i8, 10),
            c.lit(t_i8, 20),
        ),
        c.lit(t_i8, 20),
    );

    finish(&c, w);
}
