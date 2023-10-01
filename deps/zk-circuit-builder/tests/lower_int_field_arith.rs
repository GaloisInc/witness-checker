use std::convert::TryInto;
use zk_circuit_builder::eval;
use zk_circuit_builder::ir::circuit::{
    Arenas, Circuit, CircuitTrait, CircuitExt, Wire, Ty, FilterNil, GateValue, AsBits, IntSize,
    DefineFunction, TyKind, Field, UnOp, BinOp,
};
use zk_circuit_builder::lower::int_field_arith::IntFieldArith;
use zk_circuit_builder::util::CowBox;
use scuttlebutt::field::F128p;
use paste::paste;
use proptest::prelude::*;

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

macro_rules! define_unary {
    ($rust_type:ident, $ckt_type:ident) => {
        paste! {
            fn [<unary_ $rust_type _f128p>] (a: $rust_type, op: UnOp, expected: $rust_type) {
                init_circuit!(ckt_e, ckt_a);
            
                let ty = Ty::$ckt_type($rust_type::BITS as usize);
                let a_e = ckt_e.lit(ty, a);
                let res_a_e = ckt_e.unary(op, a_e);
                
                let a_a = ckt_a.lit(ty, a);
                let res_a_a = ckt_a.unary(op, a_a);
                
                let expected = eval::Value::SingleInteger(num_bigint::BigInt::from(expected));
                let source = eval::eval_wire_public(ckt_e.as_base(), res_a_e).unwrap();
                let target = eval::eval_wire_public(ckt_a.as_base(), res_a_a).unwrap();
                
                assert_eq!(expected, source);
                assert_eq!(source, target);    
            }
        }
    }
}

macro_rules! define_unary_ops {
    ($u_type:ident, $i_type:ident) => {
        paste! {
            fn [<neg_ $u_type _f128p>](a: $u_type) {
                let a_signed = a as $i_type;
                let a_neg = a_signed.wrapping_neg();
                [<unary_ $u_type _f128p>](a, UnOp::Neg, a_neg as $u_type);
            }

            fn [<neg_ $i_type _f128p>](a: $i_type) {
                let a_neg = a.wrapping_neg();
                [<unary_ $i_type _f128p>](a, UnOp::Neg, a_neg);
            }
        }
    }
}

macro_rules! define_binary {
    ($rust_type:ident, $ckt_type:ident) => {
        paste! {
            fn [<binary_ $rust_type _f128p>] (a: $rust_type, b: $rust_type, op: BinOp, expected: $rust_type) {
                init_circuit!(ckt_e, ckt_a);
            
                let ty = Ty::$ckt_type($rust_type::BITS as usize);
                let a_e = ckt_e.lit(ty, a);
                let b_e = ckt_e.lit(ty, b);
                let res_a_e = ckt_e.binary(op, a_e, b_e);
                
                let a_a = ckt_a.lit(ty, a);
                let b_a = ckt_a.lit(ty, b);
                let res_a_a = ckt_a.binary(op, a_a, b_a);
                
                let expected = eval::Value::SingleInteger(num_bigint::BigInt::from(expected));
                let source = eval::eval_wire_public(ckt_e.as_base(), res_a_e).unwrap();
                let target = eval::eval_wire_public(ckt_a.as_base(), res_a_a).unwrap();
                
                assert_eq!(expected, source);
                assert_eq!(source, target);    
            }
        }
    }
}

macro_rules! define_bin_ops {
    ($u_type:ident, $i_type:ident) => {
        paste! {
            // Add
            fn [<add_ $u_type _f128p>](a: $u_type, b: $u_type) {
                [<binary_ $u_type _f128p>](a, b, BinOp::Add, a.wrapping_add(b));
            }

            fn [<add_ $i_type _f128p>](a: $i_type, b: $i_type) {
                [<binary_ $i_type _f128p>](a, b, BinOp::Add, a.wrapping_add(b));
            }

            // Sub
            fn [<sub_ $u_type _f128p>](a: $u_type, b: $u_type) {
                [<binary_ $u_type _f128p>](a, b, BinOp::Sub, a.wrapping_sub(b));
            }

            fn [<sub_ $i_type _f128p>](a: $i_type, b: $i_type) {
                [<binary_ $i_type _f128p>](a, b, BinOp::Sub, a.wrapping_sub(b));
            }

            // Mul
            fn [<mul_ $u_type _f128p>](a: $u_type, b: $u_type) {
                [<binary_ $u_type _f128p>](a, b, BinOp::Mul, a.wrapping_mul(b));
            }

            fn [<mul_ $i_type _f128p>](a: $i_type, b: $i_type) {
                [<binary_ $i_type _f128p>](a, b, BinOp::Mul, a.wrapping_mul(b));
            }

            // Div
            fn [<div_ $u_type _f128p>](a: $u_type, b: $u_type) {
                [<binary_ $u_type _f128p>](a, b, BinOp::Div, if b == 0 { 0 } else { a / b });
            }

            fn [<div_ $i_type _f128p>](a: $i_type, b: $i_type) {
                [<binary_ $i_type _f128p>](a, b, BinOp::Div, if b == 0 { 0 } else { a / b });
            }            
        }
    }
}

define_unary!(u8, uint);
define_unary!(i8, int);
define_unary_ops!(u8, i8);

define_binary!(u8, uint);
define_binary!(i8, int);
define_bin_ops!(u8, i8);

proptest! {
    // Negation    
    #[test]
    fn lower_int_field_neg_u8_f128p(a: u8) {
        neg_u8_f128p(a)
    }

    #[test]
    fn lower_int_field_neg_i8_f128p(a: i8) {
        neg_i8_f128p(a)
    }

    #[test]
    fn lower_int_field_add_u8_f128p(a: u8, b: u8) {
        add_u8_f128p(a, b)
    }

    #[test]
    fn lower_int_field_add_i8_f128p(a: i8, b: i8) {
        add_i8_f128p(a, b)
    }

    #[test]
    fn lower_int_field_sub_u8_f128p(a: u8, b: u8) {
        sub_u8_f128p(a, b)
    }

    #[test]
    fn lower_int_field_sub_i8_f128p(a: i8, b: i8) {
        sub_i8_f128p(a, b)
    }

    #[test]
    fn lower_int_field_mul_u8_f128p(a: u8, b: u8) {
        mul_u8_f128p(a, b)
    }

    #[test]
    fn lower_int_field_mul_i8_f128p(a: i8, b: i8) {
        mul_i8_f128p(a, b)
    }
}
