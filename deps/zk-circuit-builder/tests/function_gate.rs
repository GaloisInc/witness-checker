
use std::convert::TryInto;
use zk_circuit_builder::eval;
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitExt, Wire, Ty, FilterNil, GateValue, AsBits, IntSize,
    DefineFunction,
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
    struct MyFunc;
    impl<'b> DefineFunction<'b> for MyFunc {
        fn build_body<C: CircuitTrait<'b>>(self, c: &C, args: &[Wire<'b>]) -> Wire<'b> {
            let &[x, y, z]: &[Wire; 3] = args.try_into().unwrap();
            c.add(c.mul(x, y), z)
        }
    }
    let func = c.define_function::<(), _>("f", &[ty_i32, ty_i32, ty_i32], MyFunc);

    let args1 = [
        c.lit(ty_i32, 1),
        c.lit(ty_i32, 2),
        c.lit(ty_i32, 3),
    ];
    let result1 = c.call(func, &args1, &[], |_, &(), _| (&()).into());

    let args2 = [
        c.lit(ty_i32, 4),
        c.lit(ty_i32, 5),
        c.lit(ty_i32, 6),
    ];
    let result2 = c.call(func, &args2, &[], |_, &(), _| (&()).into());

    assert_eq!(
        eval::eval_wire_public(c.as_base(), result1).unwrap(),
        eval::Value::SingleInteger(5_i32.into()),
    );

    // assert_eq!(
    //     eval::eval_wire_public(c.as_base(), result2).unwrap(),
    //     eval::Value::SingleInteger(26_i32.into()),
    // );
}

#[test]
fn function_gate_lazy_secret() {
    init_circuit!(c);

    let ty_i32 = Ty::int(32);
    struct MyFunc;
    impl<'b> DefineFunction<'b> for MyFunc {
        fn build_body<C: CircuitTrait<'b>>(self, c: &C, args: &[Wire<'b>]) -> Wire<'b> {
            let &[x]: &[Wire; 1] = args.try_into().unwrap();
            let y = c.secret_lazy(Ty::int(32), |c, &y: &i32| y.as_bits(c, IntSize(32)));
            c.add(x, y)
        }
    }
    let func = c.define_function::<i32, _>("f", &[ty_i32], MyFunc);

    // Call, with projection function returning `&'static i32`
    let args1 = [
        c.lit(ty_i32, 1),
    ];
    let result1 = c.call(func, &args1, &[], |_, &(), _| CowBox::from(&2));
    assert_eq!(
        eval::eval_wire_secret(c.as_base(), result1).unwrap(),
        eval::Value::SingleInteger(3_i32.into()),
    );
    assert!(eval::eval_wire_public(c.as_base(), result1).is_none());

    // Call, with projection function returning `Box<i32>`
    let args2 = [
        c.lit(ty_i32, 3),
    ];
    let result2 = c.call(func, &args2, &[], |_, &(), _| CowBox::from(Box::new(4)));
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
    let result3 = c.call(func, &args3, &deps3, |_, &(), dep_vals| {
        let x = dep_vals[0].0[0] as i32;
        CowBox::from(Box::new(x))
    });
    assert_eq!(
        eval::eval_wire_secret(c.as_base(), result3).unwrap(),
        eval::Value::SingleInteger(12_i32.into()),
    );
    assert!(eval::eval_wire_public(c.as_base(), result3).is_none());
}



#[test]
fn function_gate_basic_1() {

    
    init_circuit!(c);

    let ty_i32 = Ty::int(32);
    let ty_i16 = Ty::int(16);
    struct MyFunc1;
    impl<'b> DefineFunction<'b> for MyFunc1 {
        fn build_body<C: CircuitTrait<'b>>(self, c: &C, args: &[Wire<'b>]) -> Wire<'b> {
            let &[x, y, z]: &[Wire; 3] = args.try_into().unwrap();
            c.add(c.mul(x, y), z)
        }
    }

    struct MyFunc2;
    impl<'b> DefineFunction<'b> for MyFunc2 {
        fn build_body<C: CircuitTrait<'b>>(self, c: &C, args: &[Wire<'b>]) -> Wire<'b> {
            let &[x, y, z]: &[Wire; 3] = args.try_into().unwrap();
            c.mul(c.add(x, y), z)
        }
    }
    
    let func1 = c.define_function::<(), _>("func1", &[ty_i32, ty_i32, ty_i32], MyFunc1);
    let func2 = c.define_function::<(), _>("func2", &[ty_i32, ty_i32, ty_i32], MyFunc2);


    //let result = c.swich
    let args1 = [
        c.lit(ty_i32, 1),
        c.lit(ty_i32, 2),
        c.lit(ty_i32, 3),
    ];
    let call1 = c.define_call(func1, &args1, &[], |_, &(), _| (&()).into());

    let call2 = c.define_call(func2, &args1, &[], |_, &(), _| (&()).into());

    let ty_bits = Ty::int(32);
    //let ty_bits = Ty::raw_bits();


    let f1_switch_const = c.lit_(ty_bits, 10);
    let f2_switch_const = c.lit_(ty_bits, 5);

    println!("Value of x: {:?}", f1_switch_const);
    //let x = c.one();
    let branches = &[(f1_switch_const,call1), (f2_switch_const, call2)];

    //let cond = [c.lit(Ty::int(32), 5)];
    let cond = c.lit(Ty::int(32), 5);

    println!("Value of cond {:?}", cond);
    
    let result = c.switch(cond, branches, &args1);
    
    /*
    
    Doubts to ask:
    1. how to make the deps for wire<>, and &[wire<>] make work?
    2. Re-check the eval .. conversioin to int is not working... figure out why?
    */

    
    assert_eq!(
        eval::eval_wire_public(c.as_base(), result).unwrap(),
        eval::Value::SingleInteger(9_i32.into()),
    );

    /*
    assert_eq!(
        eval::eval_wire_public(c.as_base(), result2).unwrap(),
        eval::Value::SingleInteger(26_i32.into()),
    );
    */
}


// #[test]
//     fn test_addition() {
//         let result = 2 + 2;
//         println!("Result of addition: {}", result);
//         assert_eq!(result, 4);
//     }


/*
[Wire(0x7fc8ae8043e8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
Wire(0x7fc8ae804448 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
Wire(0x7fc8ae8044a8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
Wire(0x7fc8af0088d0 => Gate { ty: Ty(Int(IntSize(32))), kind: Switch(Wire(0x7fc8af008928 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([10]), 
    
Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), [(Bits([10]), Call(CallData { func: Function(FunctionDef { name: "func1", arg_tys: [Ty(Int(IntSize(32))), Ty(Int(IntSize(32))), Ty(Int(IntSize(32)))], 
result_wire: Wire(0x7fc8ae804088 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Add, Wire(0x7fc8ae8040e0), Wire(0x7fc8ae804138)), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), witness_type: TypeId { t: 3357029650088529668 } }), args: [Wire(0x7fc8ae8044a8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), Wire(0x7fc8ae804448 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), Wire(0x7fc8ae8043e8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })], project_witness: SecretProjectFn { inner: ArenaDyn(dyn zk_circuit_builder::ir::circuit::SecretProjectFnTrait<>) }, project_deps: [] })), 


(Bits([5]), Call(CallData { func: Function(FunctionDef { name: "func2", arg_tys: [Ty(Int(IntSize(32))), Ty(Int(IntSize(32))), Ty(Int(IntSize(32)))], result_wire: Wire(0x7fc8ae804538 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Mul, Wire(0x7fc8ae804590), Wire(0x7fc8ae804138)), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), witness_type: TypeId { t: 3357029650088529668 } }), args: [Wire(0x7fc8ae804350 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([4]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), Wire(0x7fc8ae8042f0 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([5]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), Wire(0x7fc8ae804290 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([6]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })], project_witness: SecretProjectFn { inner: ArenaDyn(dyn zk_circuit_builder::ir::circuit::SecretProjectFnTrait<>) }, project_deps: [] }))], [Wire(0x7fc8ae8044a8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), Wire(0x7fc8ae804448 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), Wire(0x7fc8ae8043e8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })]), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })]
*/

/*
[   Wire(0x7fafec705458 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec7054b8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec705518 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 

    Wire(0x7fafec808ed0 => Gate { ty: Ty(Int(IntSize(32))), kind: Switch(
    
    Wire(0x7fafec808f28 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([255]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    
    [
    
    (Bits([10]), Call(CallData { func: Function(FunctionDef { name: "func1", arg_tys: [Ty(Int(IntSize(32))), Ty(Int(IntSize(32))), Ty(Int(IntSize(32)))], 
    result_wire: Wire(0x7fafec7050f8 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Add, Wire(0x7fafec705150), Wire(0x7fafec7051a8)), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), witness_type: TypeId { t: 3357029650088529668 } }), 
    args: [Wire(0x7fafec705518 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec7054b8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec705458 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })], 
    project_witness: SecretProjectFn { inner: ArenaDyn(dyn zk_circuit_builder::ir::circuit::SecretProjectFnTrait<>) }, project_deps: [] })), 
    
    
    (Bits([5]), Call(CallData { func: Function(FunctionDef { name: "func2", arg_tys: [Ty(Int(IntSize(32))), Ty(Int(IntSize(32))), Ty(Int(IntSize(32)))], 
    result_wire: Wire(0x7fafec7055a8 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Mul, Wire(0x7fafec705600), Wire(0x7fafec7051a8)), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), witness_type: TypeId { t: 3357029650088529668 } }), 
    args: [Wire(0x7fafec7053c0 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([4]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec705360 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([5]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec705300 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([6]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })], 
    project_witness: SecretProjectFn { inner: ArenaDyn(dyn zk_circuit_builder::ir::circuit::SecretProjectFnTrait<>) }, project_deps: [] }))
    
    ], 
    
    
    [Wire(0x7fafec705518 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec7054b8 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fafec705458 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })]), 
    
    label: Label(""), eval_hook: Unhashed(Cell { value: None }) })
    
    ]
*/




/*
[
    // Gates w.r.t to the function or call structure.
    Wire(0x7fe6552042e0 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe655204340 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe6552043a0 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    
    Wire(0x7fe655204250 => Gate { ty: Ty(Int(IntSize(32))), kind: Call(Call(CallData { func: Function(FunctionDef { name: "f", arg_tys: [Ty(Int(IntSize(32))), Ty(Int(IntSize(32))), Ty(Int(IntSize(32)))], 
    result_wire: Wire(0x7fe655004088 => Gate { ty: Ty(Int(IntSize(32))), 
    kind: Binary(Add, Wire(0x7fe6550040e0), Wire(0x7fe655004138)), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), witness_type: TypeId { t: 3357029650088529668 } }), 
    
    args: [Wire(0x7fe6552043a0 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([1]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe655204340 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([2]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe6552042e0 => Gate { ty: Ty(Int(IntSize(32))), kind: Lit(Bits([3]), Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })], project_witness: SecretProjectFn { inner: ArenaDyn(dyn zk_circuit_builder::ir::circuit::SecretProjectFnTrait<>) }, project_deps: [] })), 
    label: Label(""), eval_hook: Unhashed(Cell { value: None }) })]



    // Gates w.r.t to the arithmetic circuits
    [Wire(0x7fe655004138 => Gate { ty: Ty(Int(IntSize(32))), kind: Argument(2, Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    
    Wire(0x7fe655004190 => Gate { ty: Ty(Int(IntSize(32))), kind: Argument(1, Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe6550041e8 => Gate { ty: Ty(Int(IntSize(32))), kind: Argument(0, Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe6550040e0 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Mul, Wire(0x7fe6550041e8 => Gate { ty: Ty(Int(IntSize(32))), kind: Argument(0, Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    Wire(0x7fe655004190 => Gate { ty: Ty(Int(IntSize(32))), kind: Argument(1, Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    
    Wire(0x7fe655004088 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Add, Wire(0x7fe6550040e0 => Gate { ty: Ty(Int(IntSize(32))), kind: Binary(Mul, Wire(0x7fe6550041e8), Wire(0x7fe655004190)), label: Label(""), eval_hook: Unhashed(Cell { value: None }) }), 
    
    Wire(0x7fe655004138 => Gate { ty: Ty(Int(IntSize(32))), kind: Argument(2, Ty(Int(IntSize(32)))), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })), label: Label(""), eval_hook: Unhashed(Cell { value: None }) })
    
    ]
*/