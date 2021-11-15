#![cfg(feature = "bellman")]

use std::path::Path;
use bumpalo::Bump;
use num_bigint::BigInt;
use cheesecloth::eval::{self, Evaluator, CachingEvaluator};
use cheesecloth::ir::circuit::{Circuit, CircuitTrait, CircuitExt, TyKind, Wire};
use cheesecloth::lower::{self, AddPass};

fn make_circuit<'a>(arena: &'a Bump) -> impl CircuitTrait<'a> + 'a {
    let c = Circuit::new(arena, true);
    let c = c.add_pass(lower::int::compare_to_greater_or_equal_to_zero);
    c
}

fn finish<'a>(c: &impl CircuitTrait<'a>, w: Wire<'a>) {
    use cheesecloth::back::zkif::backend::{Backend, Scalar};
    use std::fs::remove_file;
    use zkinterface::Reader;
    use zkinterface_bellman::zkif_backend::validate;


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
        workspace.join("constraints_0.zkif"),
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
    let c = make_circuit(&arena);
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
    let c = make_circuit(&arena);
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
