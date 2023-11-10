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
        let cf_a = IntFieldArith::<_, F128p>::new(FilterNil, true);
        let c_a = Circuit::new::<()>(&arenas_a, true, cf_a);
        let $actual = &c_a;
    }
}

macro_rules! define_unary {
    ($rust_type:ident, $ckt_type:ident) => {
        paste! {
            fn [<unary_ $rust_type _f128p>](a: $rust_type, op: UnOp, expected: $rust_type) {
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
            fn [<binary_ $rust_type _f128p>](a: $rust_type, b: $rust_type, op: BinOp, expected: $rust_type) {
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
                let target = eval::eval_wire_secret(ckt_a.as_base(), res_a_a).unwrap();
                
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
                [<binary_ $u_type _f128p>](a, b, BinOp::Div, if b == 0 { 0 } else { a.wrapping_div(b) });
            }

            fn [<div_ $i_type _f128p>](a: $i_type, b: $i_type) {
                [<binary_ $i_type _f128p>](a, b, BinOp::Div, if b == 0 { 0 } else { a.wrapping_div(b) });
            }

            // Mod
            fn [<mod_ $u_type _f128p>](a: $u_type, b: $u_type) {
                [<binary_ $u_type _f128p>](a, b, BinOp::Mod, if b == 0 { a } else { a.wrapping_rem(b) });
            }

            fn [<mod_ $i_type _f128p>](a: $i_type, b: $i_type) {
                [<binary_ $i_type _f128p>](a, b, BinOp::Mod, if b == 0 { a } else { a.wrapping_rem(b) });
            }
        }
    }
}

macro_rules! define_tests {
    ($ty:ident) => {
        paste! {
            proptest! {
                #[test]
                fn [<lower_int_field_ $ty _f128p_neg>](a: $ty) {
                    [<neg_ $ty _f128p>](a)
                }

                #[test]
                fn [<lower_int_field_ $ty _f128p_add>](a: $ty, b: $ty) {
                    [<add_ $ty _f128p>](a, b)
                }

                #[test]
                fn [<lower_int_field_ $ty _f128_sub>](a: $ty, b: $ty) {
                    [<sub_ $ty _f128p>](a, b)
                }

                #[test]
                fn [<lower_int_field_ $ty _f128p_mul>](a: $ty, b: $ty) {
                    [<mul_ $ty _f128p>](a, b)
                }

                #[test]
                fn [<lower_int_field_ $ty _f128p_div>](a: $ty, b: $ty) {
                    [<div_ $ty _f128p>](a, b)
                }

                #[test]
                fn [<lower_int_field_ $ty _f128p_mod>](a: $ty, b: $ty) {
                    [<mod_ $ty _f128p>](a, b)
                }
            }
        }
    }
}

// u8, i8
define_unary!(u8, uint);
define_unary!(i8, int);
define_unary_ops!(u8, i8);

define_binary!(u8, uint);
define_binary!(i8, int);
define_bin_ops!(u8, i8);

define_tests!(u8);
define_tests!(i8);

// u16, i16
define_unary!(u16, uint);
define_unary!(i16, int);
define_unary_ops!(u16, i16);

define_binary!(u16, uint);
define_binary!(i16, int);
define_bin_ops!(u16, i16);

define_tests!(u16);
define_tests!(i16);

// u32, i32
define_unary!(u32, uint);
define_unary!(i32, int);
define_unary_ops!(u32, i32);

define_binary!(u32, uint);
define_binary!(i32, int);
define_bin_ops!(u32, i32);

define_tests!(u32);
define_tests!(i32);

// u64, i64
define_unary!(u64, uint);
define_unary!(i64, int);
define_unary_ops!(u64, i64);

define_binary!(u64, uint);
define_binary!(i64, int);
define_bin_ops!(u64, i64);

define_tests!(u64);
define_tests!(i64);



