use std::convert::TryInto;
use zk_circuit_builder::eval;
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitExt, Wire, Ty, FilterNil, GateValue, AsBits, IntSize,
};
use zk_circuit_builder::util::CowBox;

macro_rules! init_circuit {
    ($c:ident) => {
        let arenas = Arenas::new();
        let cf = FilterNil;
        let c = Circuit::new::<()>(&arenas, true, cf);
        let $c = &c;
    };
}

#[test]
fn function_gate_basic() {
    init_circuit!(c);

    let ty_i32 = Ty::int(32);
    let func = c.define_function2::<(), _>("f", &[ty_i32, ty_i32, ty_i32], |c, args| {
        let &[x, y, z]: &[Wire; 3] = args.try_into().unwrap();
        c.add(c.mul(x, y), z)
    });

    let args1 = [
        c.lit(ty_i32, 1),
        c.lit(ty_i32, 2),
        c.lit(ty_i32, 3),
    ];
    let result1 = c.call2(func, &args1, &[], |_, &(), _| (&()).into());

    let args2 = [
        c.lit(ty_i32, 4),
        c.lit(ty_i32, 5),
        c.lit(ty_i32, 6),
    ];
    let result2 = c.call2(func, &args2, &[], |_, &(), _| (&()).into());

    assert_eq!(
        eval::eval_wire_public(c.as_base(), result1).unwrap(),
        eval::Value::SingleInteger(5_i32.into()),
    );

    assert_eq!(
        eval::eval_wire_public(c.as_base(), result2).unwrap(),
        eval::Value::SingleInteger(26_i32.into()),
    );
}

#[test]
fn function_gate_lazy_secret() {
    init_circuit!(c);

    let ty_i32 = Ty::int(32);
    let func = c.define_function2::<i32, _>("f", &[ty_i32], |c, args| {
        let &[x]: &[Wire; 1] = args.try_into().unwrap();
        let y = c.secret_lazy(ty_i32, |c, &y: &i32| y.as_bits(c, IntSize(32)));
        c.add(x, y)
    });

    // Call, with projection function returning `&'static i32`
    let args1 = [
        c.lit(ty_i32, 1),
    ];
    let result1 = c.call2(func, &args1, &[], |_, &(), _| CowBox::from(&2));
    assert_eq!(
        eval::eval_wire_secret(c.as_base(), result1).unwrap(),
        eval::Value::SingleInteger(3_i32.into()),
    );
    assert!(eval::eval_wire_public(c.as_base(), result1).is_none());

    // Call, with projection function returning `Box<i32>`
    let args2 = [
        c.lit(ty_i32, 3),
    ];
    let result2 = c.call2(func, &args2, &[], |_, &(), _| CowBox::from(Box::new(4)));
    assert_eq!(
        eval::eval_wire_secret(c.as_base(), result2).unwrap(),
        eval::Value::SingleInteger(7_i32.into()),
    );
    assert!(eval::eval_wire_public(c.as_base(), result2).is_none());

    // Call, deriving the inner secret value from wire deps
    let args3 = [
        c.lit(ty_i32, 5),
    ];
    let deps3 = [
        result2,
    ];
    let result3 = c.call2(func, &args3, &deps3, |_, &(), dep_vals| {
        let x = dep_vals[0].0[0] as i32;
        CowBox::from(Box::new(x))
    });
    assert_eq!(
        eval::eval_wire_secret(c.as_base(), result3).unwrap(),
        eval::Value::SingleInteger(12_i32.into()),
    );
    assert!(eval::eval_wire_public(c.as_base(), result3).is_none());
}
