use std::convert::TryInto;
use zk_circuit_builder::eval;
use zk_circuit_builder::ir::circuit::{Arenas, Circuit, CircuitExt, Wire, Ty, FilterNil, GateValue};

macro_rules! init_circuit {
    ($c:ident) => {
        let arenas = Arenas::new();
        let cf = FilterNil;
        let c = Circuit::new(&arenas, true, cf);
        let $c = &c;
    };
}

#[test]
fn function_gate_basic() {
    init_circuit!(c);

    let ty_i32 = Ty::int(32);
    let func = c.define_function("f", &[ty_i32, ty_i32, ty_i32], |c, args| {
        let &[x, y, z]: &[Wire; 3] = args.try_into().unwrap();
        c.add(c.mul(x, y), z)
    });

    let args1 = [
        c.lit(ty_i32, 1),
        c.lit(ty_i32, 2),
        c.lit(ty_i32, 3),
    ];
    let result1 = c.call(func, &args1, &[]);

    let args2 = [
        c.lit(ty_i32, 4),
        c.lit(ty_i32, 5),
        c.lit(ty_i32, 6),
    ];
    let result2 = c.call(func, &args2, &[]);

    assert_eq!(
        eval::eval_wire_public(c, result1).unwrap(),
        eval::Value::SingleInteger(5_i32.into()),
    );
    assert!(matches!(result1.value.get(), GateValue::Public(_)));

    assert_eq!(
        eval::eval_wire_public(c, result2).unwrap(),
        eval::Value::SingleInteger(26_i32.into()),
    );
    assert!(matches!(result2.value.get(), GateValue::Public(_)));
}

#[test]
fn function_gate_secret() {
    init_circuit!(c);

    let ty_i32 = Ty::int(32);
    let (func, (y_id, z_id)) = c.define_function_ex("f", &[ty_i32], |c, args| {
        let &[x]: &[Wire; 1] = args.try_into().unwrap();
        let (y, y_id) = c.new_secret_wire_input(ty_i32);
        let (z, z_id) = c.new_secret_wire_input(ty_i32);
        let result = c.add(c.mul(x, y), z);
        (result, (y_id, z_id))
    });

    let args1 = [
        c.lit(ty_i32, 1),
    ];
    let secrets1 = [
        (y_id, c.new_secret_init(ty_i32, || 2)),
        (z_id, c.new_secret_init(ty_i32, || 3)),
    ];
    let result1 = c.call(func, &args1, &secrets1);

    let args2 = [
        c.lit(ty_i32, 4),
    ];
    let secrets2 = [
        (y_id, c.new_secret_init(ty_i32, || 5)),
        (z_id, c.new_secret_init(ty_i32, || 6)),
    ];
    let result2 = c.call(func, &args2, &secrets2);

    assert_eq!(
        eval::eval_wire_secret(c, result1).unwrap(),
        eval::Value::SingleInteger(5_i32.into()),
    );
    assert!(eval::eval_wire_public(c, result1).is_none());
    assert!(matches!(result1.value.get(), GateValue::Secret(_)));

    assert_eq!(
        eval::eval_wire_secret(c, result2).unwrap(),
        eval::Value::SingleInteger(26_i32.into()),
    );
    assert!(eval::eval_wire_public(c, result2).is_none());
    assert!(matches!(result2.value.get(), GateValue::Secret(_)));
}
