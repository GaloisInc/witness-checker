use std::convert::TryInto;
use zk_circuit_builder::eval;
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitExt, Wire, Ty, FilterNil, GateValue, AsBits, IntSize,
    DefineFunction, TyKind, Field
};
use zk_circuit_builder::lower::int_field_arith::IntFieldArith;
use zk_circuit_builder::util::CowBox;
use scuttlebutt::field::F128p;

macro_rules! init_circuit {
    ($expected:ident, $actual:ident) => {
        let arenas_e = Arenas::new();
        let cf_e = FilterNil;
        let c_e = Circuit::new::<()>(&arenas_e, true, cf_e);
        let $expected = &c_e;

        let arenas_a = Arenas::new();
        let cf_a = IntFieldArith(FilterNil, Some(Field::F128p));
        let c_a = Circuit::new::<()>(&arenas_a, true, cf_a);
        let $actual = &c_a;
    }
}

#[test]
fn lower_neg_u32_f128p_basic() {
    init_circuit!(c_e, c_a);
    
    let u32_ty = Ty::uint(32);
    let one_e = c_e.lit(u32_ty, 1);
    let neg_one_e = c_e.neg(one_e);
    
    let one_a = c_a.lit(u32_ty, 1);
    let neg_one_a = c_a.neg(one_a);

    let expected = eval::eval_wire_public(c_e.as_base(), neg_one_e).unwrap();
    
    assert_eq!(
        expected,
        eval::eval_wire_public(c_a.as_base(), neg_one_a).unwrap(),
    );

    assert_eq!(
        expected,
        eval::Value::SingleInteger(num_bigint::BigInt::from(-1_i32 as u32)),
    );
}

#[test]
fn lower_neg_i32_f128p_basic() {
    init_circuit!(c_e, c_a);
    
    let i32_ty = Ty::int(32);
    let one_e = c_e.lit(i32_ty, 1);
    let neg_one_e = c_e.neg(one_e);
    
    let one_a = c_a.lit(i32_ty, 1);
    let neg_one_a = c_a.neg(one_a);

    let expected = eval::eval_wire_public(c_e.as_base(), neg_one_e).unwrap();
    
    assert_eq!(
        expected,
        eval::eval_wire_public(c_a.as_base(), neg_one_a).unwrap(),
    );

    assert_eq!(
        expected,
        eval::Value::SingleInteger(num_bigint::BigInt::from(-1_i32)),
    );
}

