use super::boolean::{AllocatedBit, Boolean};

use zki_sieve::producers::sink::MemorySink;
use zki_sieve::{
    consumers::evaluator::{Evaluator, PlaintextBackend},
    Source,
};
use zki_sieve::{Result, Sink};

use crate::back::sieve_ir::field::QuarkScalar;
use crate::back::sieve_ir::ir_builder::{IRBuilder, IRBuilderT};

use ff::{Field, PrimeField};
use num_bigint::BigUint;
use num_traits::{One, Zero};

fn new_builder() -> IRBuilder<MemorySink> {
    IRBuilder::new::<QuarkScalar>(MemorySink::default())
}

fn evaluate(b: IRBuilder<MemorySink>) -> Evaluator<PlaintextBackend> {
    let sink = b.finish();
    let source: Source = sink.into();
    let mut backend = PlaintextBackend::default();
    Evaluator::from_messages(source.iter_messages(), &mut backend)
}

pub fn u64_into_boolean_vec_le(
    builder: &mut IRBuilder<impl Sink + 'static>,
    value: Option<u64>,
) -> Result<Vec<Boolean>> {
    let values = match value {
        Some(ref value) => {
            let mut tmp = Vec::with_capacity(64);

            for i in 0..64 {
                tmp.push(Some(*value >> i & 1 == 1));
            }

            tmp
        }
        None => vec![None; 64],
    };

    let bits = values
        .into_iter()
        .map(|b| Boolean::alloc(builder, b))
        .collect();

    Ok(bits)
}

pub fn _field_into_boolean_vec_le<Scalar: PrimeField, S: Sink + 'static>(
    builder: &mut IRBuilder<S>,
    value: Option<Scalar>,
) -> Result<Vec<Boolean>> {
    let v = field_into_allocated_bits_le::<Scalar, S>(builder, value)?;

    Ok(v.into_iter().map(Boolean::from).collect())
}

pub fn field_into_allocated_bits_le<Scalar: PrimeField, S: Sink + 'static>(
    builder: &mut IRBuilder<S>,
    value: Option<Scalar>,
) -> Result<Vec<AllocatedBit>> {
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let field_char = Scalar::char_le_bits();
            let mut field_char = field_char.into_iter().rev();

            let mut tmp = Vec::with_capacity(Scalar::NUM_BITS as usize);

            let mut found_one = false;
            for b in value.to_le_bits().into_iter().rev().cloned() {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), Scalar::NUM_BITS as usize);

            tmp
        }
        None => vec![None; Scalar::NUM_BITS as usize],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .map(|b| AllocatedBit::alloc(builder, b))
        .collect::<Vec<_>>();

    Ok(bits)
}

macro_rules! initialize_everything {
    ($one_:ident, $zero_:ident) => {
        let $one_ = BigUint::one();
        let $zero_ = BigUint::zero();
    };
}

#[test]
fn test_bit_allocated_bit() {
    initialize_everything!(one_, zero_);

    let mut builder = new_builder();

    let v = AllocatedBit::alloc(&mut builder, Some(true));
    assert_eq!(v.get_value(), Some(true));

    let w = AllocatedBit::alloc(&mut builder, Some(false));
    assert_eq!(w.get_value(), Some(false));

    let evaluator = evaluate(builder);

    assert_eq!(evaluator.get(v.get_wire().wire()).unwrap(), &one_);
    assert_eq!(evaluator.get(w.get_wire().wire()).unwrap(), &zero_);
}

#[test]
fn test_bit_xor() {
    initialize_everything!(one_, zero_);

    for a_val in [false, true].iter() {
        for b_val in [false, true].iter() {
            let mut builder = new_builder();
            let a = AllocatedBit::alloc(&mut builder, Some(*a_val));
            let b = AllocatedBit::alloc(&mut builder, Some(*b_val));
            let c = AllocatedBit::xor(&mut builder, &a, &b);
            assert_eq!(c.get_value().unwrap(), *a_val ^ *b_val);

            let evaluator = evaluate(builder);
            assert_eq!(
                evaluator.get(a.get_wire().wire()).unwrap(),
                if *a_val { &one_ } else { &zero_ }
            );
            assert_eq!(
                evaluator.get(b.get_wire().wire()).unwrap(),
                if *b_val { &one_ } else { &zero_ }
            );

            assert_eq!(
                evaluator.get(c.get_wire().wire()).unwrap(),
                if c.get_value().unwrap() {
                    &one_
                } else {
                    &zero_
                }
            );

            assert_eq!(evaluator.get_violations().len(), 0 as usize);
        }
    }
}

#[test]
fn test_bit_and() {
    initialize_everything!(one_, zero_);

    for a_val in [false, true].iter() {
        for b_val in [false, true].iter() {
            let mut builder = new_builder();
            let a = AllocatedBit::alloc(&mut builder, Some(*a_val));
            let b = AllocatedBit::alloc(&mut builder, Some(*b_val));
            let c = AllocatedBit::and(&mut builder, &a, &b);
            assert_eq!(c.get_value().unwrap(), *a_val & *b_val);

            let evaluator = evaluate(builder);
            assert_eq!(
                evaluator.get(a.get_wire().wire()).unwrap(),
                if *a_val { &one_ } else { &zero_ }
            );
            assert_eq!(
                evaluator.get(b.get_wire().wire()).unwrap(),
                if *b_val { &one_ } else { &zero_ }
            );

            assert_eq!(
                evaluator.get(c.get_wire().wire()).unwrap(),
                if c.get_value().unwrap() {
                    &one_
                } else {
                    &zero_
                }
            );

            assert_eq!(evaluator.get_violations().len(), 0 as usize);
        }
    }
}

#[test]
fn test_bit_and_not() {
    initialize_everything!(one_, zero_);

    for a_val in [false, true].iter() {
        for b_val in [false, true].iter() {
            let mut builder = new_builder();
            let a = AllocatedBit::alloc(&mut builder, Some(*a_val));
            let b = AllocatedBit::alloc(&mut builder, Some(*b_val));
            let c = AllocatedBit::and_not(&mut builder, &a, &b);
            assert_eq!(c.get_value().unwrap(), *a_val & !*b_val);

            let evaluator = evaluate(builder);
            assert_eq!(
                evaluator.get(a.get_wire().wire()).unwrap(),
                if *a_val { &one_ } else { &zero_ }
            );
            assert_eq!(
                evaluator.get(b.get_wire().wire()).unwrap(),
                if *b_val { &one_ } else { &zero_ }
            );

            assert_eq!(
                evaluator.get(c.get_wire().wire()).unwrap(),
                if c.get_value().unwrap() {
                    &one_
                } else {
                    &zero_
                }
            );

            assert_eq!(evaluator.get_violations().len(), 0 as usize);
        }
    }
}

#[test]
fn test_bit_nor() {
    initialize_everything!(one_, zero_);

    for a_val in [false, true].iter() {
        for b_val in [false, true].iter() {
            let mut builder = new_builder();
            let a = AllocatedBit::alloc(&mut builder, Some(*a_val));
            let b = AllocatedBit::alloc(&mut builder, Some(*b_val));
            let c = AllocatedBit::nor(&mut builder, &a, &b);
            assert_eq!(c.get_value().unwrap(), !*a_val & !*b_val);

            let evaluator = evaluate(builder);
            assert_eq!(
                evaluator.get(a.get_wire().wire()).unwrap(),
                if *a_val { &one_ } else { &zero_ }
            );
            assert_eq!(
                evaluator.get(b.get_wire().wire()).unwrap(),
                if *b_val { &one_ } else { &zero_ }
            );

            assert_eq!(
                evaluator.get(c.get_wire().wire()).unwrap(),
                if c.get_value().unwrap() {
                    &one_
                } else {
                    &zero_
                }
            );

            assert_eq!(evaluator.get_violations().len(), 0);
        }
    }
}

#[test]
fn test_boolean_enforce_equal() {
    initialize_everything!(one_, zero_);

    for a_bool in [false, true].iter().cloned() {
        for b_bool in [false, true].iter().cloned() {
            for a_neg in [false, true].iter().cloned() {
                for b_neg in [false, true].iter().cloned() {
                    {
                        let mut builder = new_builder();

                        let mut a = Boolean::alloc(&mut builder, Some(a_bool));
                        let mut b = Boolean::alloc(&mut builder, Some(b_bool));

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        Boolean::enforce_equal(&mut builder, &a, &b).unwrap();

                        let evaluator = evaluate(builder);
                        assert_eq!(
                            evaluator.get_violations().len() == 0,
                            (a_bool ^ a_neg) == (b_bool ^ b_neg)
                        );
                    }
                    {
                        let mut builder = new_builder();

                        let mut a = Boolean::Constant(a_bool);
                        let mut b = Boolean::alloc(&mut builder, Some(b_bool));

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        Boolean::enforce_equal(&mut builder, &a, &b).unwrap();

                        let evaluator = evaluate(builder);
                        assert_eq!(
                            evaluator.get_violations().len() == 0,
                            (a_bool ^ a_neg) == (b_bool ^ b_neg)
                        );
                    }
                    {
                        let mut builder = new_builder();

                        let mut a = Boolean::alloc(&mut builder, Some(a_bool));
                        let mut b = Boolean::Constant(b_bool);

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        Boolean::enforce_equal(&mut builder, &a, &b).unwrap();

                        let evaluator = evaluate(builder);
                        assert_eq!(
                            evaluator.get_violations().len() == 0,
                            (a_bool ^ a_neg) == (b_bool ^ b_neg)
                        )
                    }
                    {
                        let mut builder = new_builder();

                        let mut a = Boolean::Constant(a_bool);
                        let mut b = Boolean::Constant(b_bool);

                        if a_neg {
                            a = a.not();
                        }
                        if b_neg {
                            b = b.not();
                        }

                        let result = Boolean::enforce_equal(&mut builder, &a, &b);

                        let evaluator = evaluate(builder);

                        if (a_bool ^ a_neg) == (b_bool ^ b_neg) {
                            assert!(result.is_ok());
                            assert_eq!(evaluator.get_violations().len(), 0);
                        } else {
                            assert!(result.is_err());
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn test_boolean_negation() {
    let mut builder = new_builder();

    let mut b = Boolean::alloc(&mut builder, Some(true));

    match b {
        Boolean::Is(_) => {}
        _ => panic!("unexpected value"),
    }

    b = b.not();

    match b {
        Boolean::Not(_) => {}
        _ => panic!("unexpected value"),
    }

    b = b.not();

    match b {
        Boolean::Is(_) => {}
        _ => panic!("unexpected value"),
    }

    b = Boolean::constant(true);

    match b {
        Boolean::Constant(true) => {}
        _ => panic!("unexpected value"),
    }

    b = b.not();

    match b {
        Boolean::Constant(false) => {}
        _ => panic!("unexpected value"),
    }

    b = b.not();

    match b {
        Boolean::Constant(true) => {}
        _ => panic!("unexpected value"),
    }
}

#[derive(Copy, Clone, Debug)]
enum OperandType {
    True,
    False,
    AllocatedTrue,
    AllocatedFalse,
    NegatedAllocatedTrue,
    NegatedAllocatedFalse,
}

impl OperandType {
    fn is_constant(&self) -> bool {
        match *self {
            OperandType::True => true,
            OperandType::False => true,
            OperandType::AllocatedTrue => false,
            OperandType::AllocatedFalse => false,
            OperandType::NegatedAllocatedTrue => false,
            OperandType::NegatedAllocatedFalse => false,
        }
    }

    fn val(&self) -> bool {
        match *self {
            OperandType::True => true,
            OperandType::False => false,
            OperandType::AllocatedTrue => true,
            OperandType::AllocatedFalse => false,
            OperandType::NegatedAllocatedTrue => false,
            OperandType::NegatedAllocatedFalse => true,
        }
    }
}

#[test]
fn test_boolean_xor() {
    let variants = [
        OperandType::True,
        OperandType::False,
        OperandType::AllocatedTrue,
        OperandType::AllocatedFalse,
        OperandType::NegatedAllocatedTrue,
        OperandType::NegatedAllocatedFalse,
    ];

    initialize_everything!(one_, zero_);

    for first_operand in variants.iter().cloned() {
        for second_operand in variants.iter().cloned() {
            let mut builder = new_builder();

            let a;
            let b;

            {
                let mut dyn_construct = |operand, name| match operand {
                    OperandType::True => Boolean::constant(true),
                    OperandType::False => Boolean::constant(false),
                    OperandType::AllocatedTrue => Boolean::alloc(&mut builder, Some(true)),
                    OperandType::AllocatedFalse => Boolean::alloc(&mut builder, Some(false)),
                    OperandType::NegatedAllocatedTrue => {
                        Boolean::alloc(&mut builder, Some(true)).not()
                    }
                    OperandType::NegatedAllocatedFalse => {
                        Boolean::alloc(&mut builder, Some(false)).not()
                    }
                };

                a = dyn_construct(first_operand, "a");
                b = dyn_construct(second_operand, "b");
            }

            let c = Boolean::xor(&mut builder, &a, &b);
            let c_wire = c.wire(&mut builder).wire();

            let evaluator = evaluate(builder);

            match (first_operand, second_operand, c.clone()) {
                (OperandType::True, OperandType::True, Boolean::Constant(false)) => {}
                (OperandType::True, OperandType::False, Boolean::Constant(true)) => {}
                (OperandType::True, OperandType::AllocatedTrue, Boolean::Not(_)) => {}
                (OperandType::True, OperandType::AllocatedFalse, Boolean::Not(_)) => {}
                (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Is(_)) => {}
                (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Is(_)) => {}

                (OperandType::False, OperandType::True, Boolean::Constant(true)) => {}
                (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                (OperandType::AllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {}
                (OperandType::AllocatedTrue, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (OperandType::AllocatedTrue, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }
                (
                    OperandType::AllocatedTrue,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::AllocatedTrue,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(true));
                }

                (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                (OperandType::AllocatedFalse, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }
                (OperandType::AllocatedFalse, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::AllocatedFalse,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(true));
                }
                (
                    OperandType::AllocatedFalse,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(false));
                }

                (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::AllocatedTrue,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::AllocatedFalse,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(true));
                }
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }

                (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::AllocatedTrue,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(true));
                }
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::AllocatedFalse,
                    Boolean::Not(ref v),
                ) => {
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }

                _ => panic!("this should never be encountered"),
            }
            assert_eq!(evaluator.get_violations().len(), 0);
        }
    }
}

#[test]
fn test_boolean_and() {
    let variants = [
        OperandType::True,
        OperandType::False,
        OperandType::AllocatedTrue,
        OperandType::AllocatedFalse,
        OperandType::NegatedAllocatedTrue,
        OperandType::NegatedAllocatedFalse,
    ];

    initialize_everything!(one_, zero_);

    for first_operand in variants.iter().cloned() {
        for second_operand in variants.iter().cloned() {
            let mut builder = new_builder();

            let a;
            let b;

            {
                let mut dyn_construct = |operand, name| match operand {
                    OperandType::True => Boolean::constant(true),
                    OperandType::False => Boolean::constant(false),
                    OperandType::AllocatedTrue => Boolean::alloc(&mut builder, Some(true)),
                    OperandType::AllocatedFalse => Boolean::alloc(&mut builder, Some(false)),
                    OperandType::NegatedAllocatedTrue => {
                        Boolean::alloc(&mut builder, Some(true)).not()
                    }
                    OperandType::NegatedAllocatedFalse => {
                        Boolean::alloc(&mut builder, Some(false)).not()
                    }
                };

                a = dyn_construct(first_operand, "a");
                b = dyn_construct(second_operand, "b");
            }

            let c = Boolean::and(&mut builder, &a, &b);
            let c_wire = c.wire(&mut builder).wire();

            let evaluator = evaluate(builder);

            match (first_operand, second_operand, c.clone()) {
                (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                (OperandType::True, OperandType::False, Boolean::Constant(false)) => {}
                (OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                (OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                (OperandType::False, OperandType::True, Boolean::Constant(false)) => {}
                (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                (OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {}
                (OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {}
                (
                    OperandType::False,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Constant(false),
                ) => {}
                (
                    OperandType::False,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Constant(false),
                ) => {}

                (OperandType::AllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                (OperandType::AllocatedTrue, OperandType::False, Boolean::Constant(false)) => {}
                (OperandType::AllocatedTrue, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }
                (OperandType::AllocatedTrue, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::AllocatedTrue,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::AllocatedTrue,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }

                (OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                (OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {}
                (OperandType::AllocatedFalse, OperandType::AllocatedTrue, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (OperandType::AllocatedFalse, OperandType::AllocatedFalse, Boolean::Is(ref v)) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::AllocatedFalse,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::AllocatedFalse,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }

                (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::False,
                    Boolean::Constant(false),
                ) => {}
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::AllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::AllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedTrue,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }

                (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::False,
                    Boolean::Constant(false),
                ) => {}
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::AllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::AllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::NegatedAllocatedTrue,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                    assert_eq!(v.get_value(), Some(false));
                }
                (
                    OperandType::NegatedAllocatedFalse,
                    OperandType::NegatedAllocatedFalse,
                    Boolean::Is(ref v),
                ) => {
                    assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                    assert_eq!(v.get_value(), Some(true));
                }

                _ => {
                    panic!(
                        "unexpected behavior at {:?} AND {:?}",
                        first_operand, second_operand
                    );
                }
            }
            assert_eq!(evaluator.get_violations().len(), 0);
        }
    }
}

#[test]
fn test_u64_into_boolean_vec_le() {
    initialize_everything!(one_, zero_);
    let mut builder = new_builder();

    let bits = u64_into_boolean_vec_le(&mut builder, Some(17234652694787248421)).unwrap();

    let evaluator = evaluate(builder);
    assert_eq!(evaluator.get_violations().len(), 0);

    assert_eq!(bits.len(), 64);

    assert_eq!(bits[63 - 0].get_value().unwrap(), true);
    assert_eq!(bits[63 - 1].get_value().unwrap(), true);
    assert_eq!(bits[63 - 2].get_value().unwrap(), true);
    assert_eq!(bits[63 - 3].get_value().unwrap(), false);
    assert_eq!(bits[63 - 4].get_value().unwrap(), true);
    assert_eq!(bits[63 - 5].get_value().unwrap(), true);
    assert_eq!(bits[63 - 20].get_value().unwrap(), true);
    assert_eq!(bits[63 - 21].get_value().unwrap(), false);
    assert_eq!(bits[63 - 22].get_value().unwrap(), false);
}

#[test]
fn test_field_into_allocated_bits_le() {
    initialize_everything!(one_, zero_);
    let mut builder = new_builder();

    let r = QuarkScalar::from_str("139407991430939255523467833655006660152").unwrap();

    let bits = field_into_allocated_bits_le(&mut builder, Some(r)).unwrap();

    let evaluator = evaluate(builder);
    assert_eq!(evaluator.get_violations().len(), 0);

    assert_eq!(bits.len(), 128);

    assert_eq!(bits[127 - 4].get_value().unwrap(), true);
    assert_eq!(bits[127 - 7].get_value().unwrap(), false);
    assert_eq!(bits[127 - 16].get_value().unwrap(), false);
    assert_eq!(bits[127 - 20].get_value().unwrap(), false);
    assert_eq!(bits[127 - 29].get_value().unwrap(), true);
    assert_eq!(bits[127 - 37].get_value().unwrap(), false);
    assert_eq!(bits[127 - 47].get_value().unwrap(), true);
    assert_eq!(bits[127 - 60].get_value().unwrap(), false);
    assert_eq!(bits[127 - 74].get_value().unwrap(), false);
}
