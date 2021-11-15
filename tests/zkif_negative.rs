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
fn add_neg_one() {
    let arena = Bump::new();
    let c = make_circuit(&arena);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.add(c.lit(t_u8, 100), c.lit(t_u8, 0xff)),
        c.lit(t_u8, 99),
    );

    finish(&c, w);
}

#[test]
fn add_neg_one_u64() {
    let arena = Bump::new();
    let c = make_circuit(&arena);
    let t_u64 = c.ty(TyKind::U64);

    let w = c.eq(
        c.add(c.lit(t_u64, 100), c.lit(t_u64, 0xffff_ffff_ffff_ffff_u64)),
        c.lit(t_u64, 99),
    );

    finish(&c, w);
}

/// Divide a number by a large denominator.  A case like this can occur when dividing by negative
/// one.
#[test]
fn div_large() {
    let arena = Bump::new();
    let c = make_circuit(&arena);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.div(c.lit(t_u8, 100), c.lit(t_u8, 229)),
        c.lit(t_u8, 0),
    );

    finish(&c, w);
}

#[test]
fn neg_one() {
    let arena = Bump::new();
    let c = make_circuit(&arena);
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
    let c = make_circuit(&arena);
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
    let c = make_circuit(&arena);
    let t_i8 = c.ty(TyKind::I8);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.shr(c.lit(t_i8, -1), c.lit(t_u8, 1)),
        c.lit(t_i8, -1),
    );

    finish(&c, w);
}

#[test]
fn neg_one_shl() {
    let arena = Bump::new();
    let c = make_circuit(&arena);
    let t_i8 = c.ty(TyKind::I8);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.shl(c.lit(t_i8, -1), c.lit(t_u8, 1)),
        c.lit(t_i8, -2),
    );

    finish(&c, w);
}
