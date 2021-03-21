// Inspired from bellman::gadgets::boolean

use ff::PrimeField;
use zki_sieve::{
    WireId,
    Result,
    producers::build_gates::BuildGate::*,
};
use zki_sieve::producers::builder::{IBuilder, BuildGate};
use zkinterface_bellman::bellman::gadgets::Assignment;
use num_traits::AsPrimitive;
use std::io::Write;

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone)]
pub struct AllocatedBit {
    wire: WireId,
    value: Option<bool>,
}

fn write_scalar<Scalar: PrimeField>(
    fr: &Scalar,
    writer: &mut impl Write,
) {
    let repr = fr.to_repr();
    writer.write_all(repr.as_ref()).unwrap();
}

fn minus_one<Scalar: PrimeField>() -> Vec<u8> {
    let negative_one = Scalar::one();
    negative_one.neg();

    let mut minus_one = Vec::<u8>::new();
    write_scalar(&negative_one, &mut minus_one);
    minus_one
}

fn one<Scalar: PrimeField>() -> Vec<u8> {

    let mut one = Vec::<u8>::new();
    write_scalar(&Scalar::one(), &mut one);
    one
}

impl AllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_wire(&self) -> WireId {
        self.wire
    }

    pub fn alloc<Builder>(mut builder: &mut Builder, value: Option<bool>) -> Result<(Self)>
    where
        Builder: IBuilder
    {
        let allocated = builder.create_gate(
            BuildGate::Constant(vec![value.unwrap_or(false).as_()])
        );

        Ok(AllocatedBit {
            wire: allocated,
            value,
        })
    }


    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor<Scalar, Builder>(mut builder: &mut Builder, a: &Self, b: &Self) -> Result<(Self)>
    where
        Scalar: PrimeField,
        Builder: IBuilder
    {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(a_val ^ b_val), // prover mode
            _ => None // verifier mode
        };

        // Implementing XOR using arithmetic operations only:
        // Truth Table:
        //  a | b | a^b | (a-b)*(a-b)
        // ---|---|-----|------------|
        //  0 | 0 |  0  |     0
        //  0 | 1 |  1  |     1
        //  1 | 0 |  1  |     1
        //  1 | 1 |  0  |     0

        let minus_one_wire = builder.create_gate(Constant(minus_one::<Scalar>()));
        let minus_b_wire = builder.create_gate(Mul(minus_one_wire, b.get_wire()));
        let tmp_wire = builder.create_gate(Add(a.get_wire(), minus_b_wire));
        let result_wire = builder.create_gate(Mul(tmp_wire, tmp_wire));

        Ok(AllocatedBit {
            wire: result_wire,
            value: result_value,
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and<Scalar, Builder>(mut builder: &mut Builder, a: &Self, b: &Self) -> Result<(Self)>
    where
        Scalar: PrimeField,
        Builder: IBuilder
    {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(a_val & b_val), // prover mode
            _ => None // verifier mode
        };

        // Implementing AND using arithmetic operations only:
        // Truth Table:
        //  a | b | a&b | a*b
        // ---|---|-----|-----|
        //  0 | 0 |  0  |  0
        //  0 | 1 |  0  |  0
        //  1 | 0 |  0  |  0
        //  1 | 1 |  1  |  1
        let wire = builder.create_gate(Mul(a.get_wire(), b.get_wire()));

        Ok(AllocatedBit {
            wire,
            value: result_value,
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<Scalar, Builder>(mut builder: &mut Builder, a: &Self, b: &Self) -> Result<(Self)>
    where
        Scalar: PrimeField,
        Builder: IBuilder
    {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(a_val & !b_val), // prover mode
            _ => None // verifier mode
        };

        // Implementing AND-NOT using arithmetic operations only:
        // Truth Table:
        //  a | b | a&!b | a - a*b
        // ---|---|------|--------|
        //  0 | 0 |  0   |  0
        //  0 | 1 |  0   |  0
        //  1 | 0 |  1   |  1
        //  1 | 1 |  0   |  0
        let minus_one_wire = builder.create_gate(Constant(minus_one::<Scalar>()));
        let ab_wire = builder.create_gate(Mul(a.get_wire(), b.get_wire()));
        let minus_ab_wire = builder.create_gate(Mul(minus_one_wire, ab_wire));
        let wire = builder.create_gate(Add(a.get_wire(), minus_ab_wire));

        Ok(AllocatedBit {
            wire,
            value: result_value,
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<Scalar, Builder>(mut builder: &mut Builder, a: &Self, b: &Self) -> Result<(Self)>
    where
        Scalar: PrimeField,
        Builder: IBuilder
    {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(!a_val & !b_val), // prover mode
            _ => None // verifier mode
        };

        // Implementing NOR using arithmetic operations only:
        // Truth Table:
        //  a | b | !a & !b |(1-a)*(1-b)
        // ---|---|---------|-----------|
        //  0 | 0 |    1    |     1
        //  0 | 1 |    0    |     0
        //  1 | 0 |    0    |     0
        //  1 | 1 |    0    |     0
        let minus_one_wire = builder.create_gate(Constant(minus_one::<Scalar>()));
        let minus_a_wire = builder.create_gate(Mul(minus_one_wire, a.get_wire()));
        let minus_b_wire = builder.create_gate(Mul(minus_one_wire, b.get_wire()));

        let one_wire = builder.create_gate(Constant(one::<Scalar>()));
        let left_wire = builder.create_gate(Add(one_wire, minus_a_wire));
        let right_wire = builder.create_gate(Add(one_wire, minus_b_wire));
        let wire = builder.create_gate(Mul(left_wire, right_wire));

        Ok(AllocatedBit {
            wire,
            value: result_value,
        })
    }
}

pub fn u64_into_boolean_vec_le<Scalar, Builder>(mut builder: &mut Builder, value: Option<u64>) -> Result<(Vec<Boolean>)>
where
    Scalar: PrimeField,
    Builder: IBuilder
{
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
        .map(|b| {
            Ok(Boolean::from(AllocatedBit::alloc(
                builder,
                b,
            )?))
        })
        .collect::<Result<(Vec<_>)>>()?;

    Ok(bits)
}

pub fn field_into_boolean_vec_le<
    Scalar: PrimeField,
    Builder: IBuilder,
>(
    mut builder: &mut Builder,
    value: Option<Scalar>,
) -> Result<(Vec<Boolean>)>
{
    let v = field_into_allocated_bits_le::<Scalar, Builder>(builder, value)?;

    Ok(v.into_iter().map(Boolean::from).collect())
}

pub fn field_into_allocated_bits_le<
    Scalar: PrimeField,
    Builder: IBuilder,
>(
    mut builder: &mut Builder,
    value: Option<Scalar>,
) -> Result<(Vec<AllocatedBit>)> {
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
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(builder, b))
        .collect::<Result<(Vec<_>)>>()?;

    Ok(bits)
}

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone)]
pub enum Boolean {
    /// Existential view of the boolean variable
    Is(AllocatedBit),
    /// Negated view of the boolean variable
    Not(AllocatedBit),
    /// Constant (not an allocated variable)
    Constant(bool),
}

impl Boolean {
    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false,
        }
    }

    pub fn enforce_equal<'l, Scalar, Builder>(mut builder: &mut Builder, a: &'l Self, b: &'l Self) -> Result<()>
        where
            Scalar: PrimeField,
            Builder: IBuilder,
    {
        match (a, b) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err("Unsatisfiable".into())
                }
            }
            (&Boolean::Constant(true), c) | (c, &Boolean::Constant(true)) => {
                match &c {
                    Boolean::Is(ref v) => {
                        let w = builder.create_gate(Not(v.get_wire()));
                        builder.create_gate(AssertZero(w));
                    },
                    Boolean::Not(ref v) => {
                        builder.create_gate(AssertZero(v.get_wire()));
                    },
                    _ => { /* This case will never happen => DO NOTHING */ }
                }
                Ok(())
            }
            (&Boolean::Constant(false), c) | (c, &Boolean::Constant(false)) => {
                match &c {
                    Boolean::Is(ref v) => {
                        builder.create_gate(AssertZero(v.get_wire()));
                    },
                    Boolean::Not(ref v) => {
                        let w = builder.create_gate(Not(v.get_wire()));
                        builder.create_gate(AssertZero(w));
                    },
                    _ => { /* This case will never happen => DO NOTHING */ }
                }
                Ok(())
            }
            (&Boolean::Is(ref v), &Boolean::Is(ref w)) | (&Boolean::Not(ref v), &Boolean::Not(ref w)) => {
                let xorwire = AllocatedBit::xor::<Scalar, Builder>(builder, &v, &w)?.get_wire();
                builder.create_gate(AssertZero(xorwire));

                Ok(())
            }

            (&Boolean::Is(ref v), &Boolean::Not(ref w)) | (&Boolean::Not(ref v), &Boolean::Is(ref w)) => {
                let norwire = AllocatedBit::nor::<Scalar, Builder>(builder, &v, &w)?.get_wire();
                builder.create_gate(AssertZero(norwire));

                Ok(())
            }
        }
    }

    pub fn get_value(&self) -> Option<bool> {
        match *self {
            Boolean::Constant(c) => Some(c),
            Boolean::Is(ref v) => v.get_value(),
            Boolean::Not(ref v) => v.get_value().map(|b| !b),
        }
    }

    /// Construct a boolean from a known constant
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// Return a negated interpretation of this boolean.
    pub fn not(&self) -> Self {
        match *self {
            Boolean::Constant(c) => Boolean::Constant(!c),
            Boolean::Is(ref v) => Boolean::Not(v.clone()),
            Boolean::Not(ref v) => Boolean::Is(v.clone()),
        }
    }

    /// Perform XOR over two boolean operands
    pub fn xor<'a, Scalar, Builder>(mut builder: &mut Builder, a: &'a Self, b: &'a Self) -> Result<(Self)>
        where
            Scalar: PrimeField,
            Builder: IBuilder,
    {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_))
            | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Ok(Boolean::xor::<Scalar, Builder>(builder, is, &not.not())?.not())
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b))
            | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::xor::<Scalar, Builder>(builder, a, b)?))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a, Scalar, Builder>(mut builder: &mut Builder, a: &'a Self, b: &'a Self) -> Result<(Self)>
        where
            Scalar: PrimeField,
            Builder: IBuilder,
    {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => {
                Ok(Boolean::Constant(false))
            }
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.clone()),
            // a AND (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not))
            | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Ok(Boolean::Is(AllocatedBit::and_not::<Scalar, Builder>(builder, is, not)?))
            }
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::nor::<Scalar, Builder>(builder, a, b)?))
            }
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::and::<Scalar, Builder>(builder, a, b)?))
            }
        }
    }

}

impl From<AllocatedBit> for Boolean {
    fn from(b: AllocatedBit) -> Boolean {
        Boolean::Is(b)
    }
}


#[cfg(test)]
mod test {
/*
    use super::{field_into_allocated_bits_le, u64_into_boolean_vec_le, AllocatedBit, Boolean};
    use crate::gadgets::test::*;

    use zki_sieve::producers::builder::Builder;
    use zki_sieve::producers::examples::*;
    use ff::{Field, PrimeField};
    use crate::back::sieve_ir::field::QuarkScalar;

    type Scalar = QuarkScalar;

    #[test]
    fn test_allocated_bit() {
        let mut builder = Builder::new(0);
        let header = example_header_in_field();



        AllocatedBit::alloc(&mut cs, Some(true)).unwrap();
        assert!(cs.get("boolean") == Scalar::one());
        assert!(cs.is_satisfied());
        cs.set("boolean", Scalar::zero());
        assert!(cs.is_satisfied());
        cs.set("boolean", Scalar::from_str("2").unwrap());
        assert!(!cs.is_satisfied());
        assert!(cs.which_is_unsatisfied() == Some("boolean constraint"));
    }

    #[test]
    fn test_xor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::xor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val ^ *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("xor result")
                        == if *a_val ^ *b_val {
                        Field::one()
                    } else {
                        Field::zero()
                    }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "xor result",
                    if *a_val ^ *b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::and(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("and result")
                        == if *a_val & *b_val {
                        Field::one()
                    } else {
                        Field::zero()
                    }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and result",
                    if *a_val & *b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_and_not() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::and_not(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("and not result")
                        == if *a_val & !*b_val {
                        Field::one()
                    } else {
                        Field::zero()
                    }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and not result",
                    if *a_val & !*b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_nor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Scalar>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::nor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !*a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("nor result")
                        == if !*a_val & !*b_val {
                        Field::one()
                    } else {
                        Field::zero()
                    }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "nor result",
                    if !*a_val & !*b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_enforce_equal() {
        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        {
                            let mut cs = TestConstraintSystem::<Scalar>::new();

                            let mut a = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "a"), Some(a_bool)).unwrap(),
                            );
                            let mut b = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "b"), Some(b_bool)).unwrap(),
                            );

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                        }
                        {
                            let mut cs = TestConstraintSystem::<Scalar>::new();

                            let mut a = Boolean::Constant(a_bool);
                            let mut b = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "b"), Some(b_bool)).unwrap(),
                            );

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                        }
                        {
                            let mut cs = TestConstraintSystem::<Scalar>::new();

                            let mut a = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "a"), Some(a_bool)).unwrap(),
                            );
                            let mut b = Boolean::Constant(b_bool);

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                        }
                        {
                            let mut cs = TestConstraintSystem::<Scalar>::new();

                            let mut a = Boolean::Constant(a_bool);
                            let mut b = Boolean::Constant(b_bool);

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            let result = Boolean::enforce_equal(&mut cs, &a, &b);

                            if (a_bool ^ a_neg) == (b_bool ^ b_neg) {
                                assert!(result.is_ok());
                                assert!(cs.is_satisfied());
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
        let mut cs = TestConstraintSystem::<Scalar>::new();

        let mut b = Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap());

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

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Scalar>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::xor(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
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
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    _ => panic!("this should never be encountered"),
                }
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

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Scalar>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::and(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {
                    }
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
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
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
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
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
                        assert!(cs.get("and not result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    _ => {
                        panic!(
                            "unexpected behavior at {:?} AND {:?}",
                            first_operand, second_operand
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_u64_into_boolean_vec_le() {
        let mut cs = TestConstraintSystem::<Scalar>::new();

        let bits = u64_into_boolean_vec_le(&mut cs, Some(17234652694787248421)).unwrap();

        assert!(cs.is_satisfied());

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
        let mut cs = TestConstraintSystem::<Scalar>::new();

        let r = Scalar::from_str(
            "9147677615426976802526883532204139322118074541891858454835346926874644257775",
        )
            .unwrap();

        let bits = field_into_allocated_bits_le(&mut cs, Some(r)).unwrap();

        assert!(cs.is_satisfied());

        assert_eq!(bits.len(), 255);

        assert_eq!(bits[254 - 0].value.unwrap(), false);
        assert_eq!(bits[254 - 1].value.unwrap(), false);
        assert_eq!(bits[254 - 2].value.unwrap(), true);
        assert_eq!(bits[254 - 3].value.unwrap(), false);
        assert_eq!(bits[254 - 4].value.unwrap(), true);
        assert_eq!(bits[254 - 5].value.unwrap(), false);
        assert_eq!(bits[254 - 20].value.unwrap(), true);
        assert_eq!(bits[254 - 23].value.unwrap(), true);
    }

    #[test]
    fn test_boolean_sha256_ch() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    let mut cs = TestConstraintSystem::new();

                    let a;
                    let b;
                    let c;

                    // ch = (a and b) xor ((not a) and c)
                    let expected = (first_operand.val() & second_operand.val())
                        ^ ((!first_operand.val()) & third_operand.val());

                    {
                        let mut dyn_construct = |operand, name| {
                            let cs = cs.namespace(|| name);

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                }
                                OperandType::AllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                }
                                OperandType::NegatedAllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                        .not()
                                }
                                OperandType::NegatedAllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                        .not()
                                }
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        c = dyn_construct(third_operand, "c");
                    }

                    let maj = Boolean::sha256_ch(&mut cs, &a, &b, &c).unwrap();

                    assert!(cs.is_satisfied());

                    assert_eq!(maj.get_value().unwrap(), expected);

                    if first_operand.is_constant()
                        || second_operand.is_constant()
                        || third_operand.is_constant()
                    {
                        if first_operand.is_constant()
                            && second_operand.is_constant()
                            && third_operand.is_constant()
                        {
                            assert_eq!(cs.num_constraints(), 0);
                        }
                    } else {
                        assert_eq!(cs.get("ch"), {
                            if expected {
                                Scalar::one()
                            } else {
                                Scalar::zero()
                            }
                        });
                        cs.set("ch", {
                            if expected {
                                Scalar::zero()
                            } else {
                                Scalar::one()
                            }
                        });
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "ch computation");
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_sha256_maj() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    let mut cs = TestConstraintSystem::new();

                    let a;
                    let b;
                    let c;

                    // maj = (a and b) xor (a and c) xor (b and c)
                    let expected = (first_operand.val() & second_operand.val())
                        ^ (first_operand.val() & third_operand.val())
                        ^ (second_operand.val() & third_operand.val());

                    {
                        let mut dyn_construct = |operand, name| {
                            let cs = cs.namespace(|| name);

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                }
                                OperandType::AllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                }
                                OperandType::NegatedAllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                        .not()
                                }
                                OperandType::NegatedAllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                        .not()
                                }
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        c = dyn_construct(third_operand, "c");
                    }

                    let maj = Boolean::sha256_maj(&mut cs, &a, &b, &c).unwrap();

                    assert!(cs.is_satisfied());

                    assert_eq!(maj.get_value().unwrap(), expected);

                    if first_operand.is_constant()
                        || second_operand.is_constant()
                        || third_operand.is_constant()
                    {
                        if first_operand.is_constant()
                            && second_operand.is_constant()
                            && third_operand.is_constant()
                        {
                            assert_eq!(cs.num_constraints(), 0);
                        }
                    } else {
                        assert_eq!(cs.get("maj"), {
                            if expected {
                                Scalar::one()
                            } else {
                                Scalar::zero()
                            }
                        });
                        cs.set("maj", {
                            if expected {
                                Scalar::zero()
                            } else {
                                Scalar::one()
                            }
                        });
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "maj computation");
                    }
                }
            }
        }
    }

    #[test]
    fn test_alloc_conditionally() {
        {
            let mut cs = TestConstraintSystem::<Scalar>::new();
            let b = AllocatedBit::alloc(&mut cs, Some(false)).unwrap();

            let value = None;
            // if value is none, fail with SynthesisError
            let is_err = AllocatedBit::alloc_conditionally(
                cs.namespace(|| "alloc_conditionally"),
                value,
                &b,
            )
                .is_err();
            assert!(is_err);
        }

        {
            // since value is true, b must be false, so it should succeed
            let mut cs = TestConstraintSystem::<Scalar>::new();

            let value = Some(true);
            let b = AllocatedBit::alloc(&mut cs, Some(false)).unwrap();
            let allocated_value = AllocatedBit::alloc_conditionally(
                cs.namespace(|| "alloc_conditionally"),
                value,
                &b,
            )
                .unwrap();

            assert_eq!(allocated_value.get_value().unwrap(), true);
            assert!(cs.is_satisfied());
        }

        {
            // since value is true, b must be false, so it should fail
            let mut cs = TestConstraintSystem::<Scalar>::new();

            let value = Some(true);
            let b = AllocatedBit::alloc(&mut cs, Some(true)).unwrap();
            AllocatedBit::alloc_conditionally(cs.namespace(|| "alloc_conditionally"), value, &b)
                .unwrap();

            assert!(!cs.is_satisfied());
        }

        {
            // since value is false, we don't care about the value of the bit

            let value = Some(false);
            //check with false bit
            let mut cs = TestConstraintSystem::<Scalar>::new();
            let b1 = AllocatedBit::alloc(&mut cs, Some(false)).unwrap();
            AllocatedBit::alloc_conditionally(cs.namespace(|| "alloc_conditionally"), value, &b1)
                .unwrap();

            assert!(cs.is_satisfied());

            //check with true bit
            let mut cs = TestConstraintSystem::<Scalar>::new();
            let b2 = AllocatedBit::alloc(&mut cs, Some(true)).unwrap();
            AllocatedBit::alloc_conditionally(cs.namespace(|| "alloc_conditionally"), value, &b2)
                .unwrap();

            assert!(cs.is_satisfied());
        }
    }

*/
}

