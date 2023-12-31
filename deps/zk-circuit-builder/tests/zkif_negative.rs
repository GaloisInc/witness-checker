#![cfg(feature = "bellman")]

use num_bigint::BigInt;
use zk_circuit_builder::eval::{self, EvalWire, CachingEvaluator};
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitExt, CircuitFilter, FilterNil, TyKind, Wire,
};
use zk_circuit_builder::lower;

macro_rules! make_circuit {
    ($arenas:expr) => {{
        let cf = FilterNil.add_pass(lower::int::compare_to_greater_or_equal_to_zero);
        let c = Circuit::new::<()>($arenas, true, cf);
        c
    }};
}

fn finish<'a, C: CircuitTrait<'a> + ?Sized>(c: &'a C, w: Wire<'a>) {
    use zk_circuit_builder::back::zkif::backend::{Backend, Scalar};
    use std::fs::remove_file;
    use zkinterface::Reader;
    use zkinterface_bellman::zkif_backend::validate;


    // Make sure the circuit is valid.
    let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
    let val = ev.eval_wire(c, w).ok();
    assert_eq!(val, Some(eval::Value::SingleInteger(BigInt::from(1))));


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
    backend.enforce_true(c.as_base(), &mut ev, w);
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
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.add(c.lit(t_u8, 100), c.lit(t_u8, 0xff)),
        c.lit(t_u8, 99),
    );

    finish(&c, w);
}

#[test]
fn add_neg_one_u64() {
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
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
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.div(c.lit(t_u8, 100), c.lit(t_u8, 229)),
        c.lit(t_u8, 0),
    );

    finish(&c, w);
}

#[test]
fn neg_one() {
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.neg(c.lit(t_i8, 1)),
        c.lit(t_i8, -1),
    );

    finish(&c, w);
}

#[test]
fn not_zero() {
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    let t_i8 = c.ty(TyKind::I8);

    let w = c.eq(
        c.not(c.lit(t_i8, 0)),
        c.lit(t_i8, -1),
    );

    finish(&c, w);
}

#[test]
fn neg_one_shr() {
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
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
    let arenas = Arenas::new();
    let c = make_circuit!(&arenas);
    let t_i8 = c.ty(TyKind::I8);
    let t_u8 = c.ty(TyKind::U8);

    let w = c.eq(
        c.shl(c.lit(t_i8, -1), c.lit(t_u8, 1)),
        c.lit(t_i8, -2),
    );

    finish(&c, w);
}
