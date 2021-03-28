// Inspired from bellman::gadgets::boolean

use ff::PrimeField;
use zki_sieve::{Result, WireId};

use crate::back::sieve_ir::builder_ext::BuilderExt;

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone)]
pub struct AllocatedBit {
    wire: WireId,
    value: Option<bool>,
}

impl AllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_wire(&self) -> WireId {
        self.wire
    }

    pub fn alloc(b: &mut BuilderExt, value: Option<bool>) -> Result<Self> {
        let field_value = match value {
            Some(false) => Some(vec![0]),
            Some(true) => Some(vec![1]),
            None => None,
        };
        let wire = b.new_witness(field_value);

        // (x - 1) * x == 0
        let wire_1 = b.add(wire, b.neg_one);
        let prod = b.mul(wire, wire_1);
        b.assert_zero(prod);

        Ok(AllocatedBit { wire, value })
    }

    /// Calculates `NOT a`.
    pub fn not(b: &mut BuilderExt, a: &Self) -> Self {
        let value = match a.value {
            Some(a_val) => Some(!a_val), // prover mode
            _ => None,                   // verifier mode
        };

        // Implementing NOT using arithmetic operations only:
        // Truth Table:
        //  a | 1 - a |
        // ---|-------|
        //  0 | 1     |
        //  1 | 0     |
        let wire = b.sub(b.one, a.get_wire());

        AllocatedBit { wire, value }
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor(builder: &mut BuilderExt, a: &Self, b: &Self) -> Result<Self> {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(a_val ^ b_val), // prover mode
            _ => None,                                         // verifier mode
        };

        // Implementing XOR using arithmetic operations only:
        // Truth Table:
        //  a | b | a^b | (a-b)*(a-b)
        // ---|---|-----|------------|
        //  0 | 0 |  0  |     0
        //  0 | 1 |  1  |     1
        //  1 | 0 |  1  |     1
        //  1 | 1 |  0  |     0

        let tmp_wire = builder.sub(a.get_wire(), b.get_wire());
        let result_wire = builder.mul(tmp_wire, tmp_wire);

        Ok(AllocatedBit {
            wire: result_wire,
            value: result_value,
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and(builder: &mut BuilderExt, a: &Self, b: &Self) -> Result<Self> {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(a_val & b_val), // prover mode
            _ => None,                                         // verifier mode
        };

        // Implementing AND using arithmetic operations only:
        // Truth Table:
        //  a | b | a&b | a*b
        // ---|---|-----|-----|
        //  0 | 0 |  0  |  0
        //  0 | 1 |  0  |  0
        //  1 | 0 |  0  |  0
        //  1 | 1 |  1  |  1
        let wire = builder.mul(a.get_wire(), b.get_wire());

        Ok(AllocatedBit {
            wire,
            value: result_value,
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not(builder: &mut BuilderExt, a: &Self, b: &Self) -> Result<Self> {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(a_val & !b_val), // prover mode
            _ => None,                                          // verifier mode
        };

        // Implementing AND-NOT using arithmetic operations only:
        // Truth Table:
        //  a | b | a&!b | a*(1-b)
        // ---|---|------|--------|
        //  0 | 0 |  0   |  0
        //  0 | 1 |  0   |  0
        //  1 | 0 |  1   |  1
        //  1 | 1 |  0   |  0
        let right_wire = builder.sub(builder.one, b.get_wire());
        let wire = builder.mul(a.get_wire(), right_wire);

        Ok(AllocatedBit {
            wire,
            value: result_value,
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor(builder: &mut BuilderExt, a: &Self, b: &Self) -> Result<Self> {
        let result_value = match (a.value, b.value) {
            (Some(a_val), Some(b_val)) => Some(!a_val & !b_val), // prover mode
            _ => None,                                           // verifier mode
        };

        // Implementing NOR using arithmetic operations only:
        // Truth Table:
        //  a | b | !a & !b |(1-a)*(1-b)
        // ---|---|---------|-----------|
        //  0 | 0 |    1    |     1
        //  0 | 1 |    0    |     0
        //  1 | 0 |    0    |     0
        //  1 | 1 |    0    |     0
        let left_wire = builder.sub(builder.one, a.get_wire());
        let right_wire = builder.sub(builder.one, b.get_wire());
        let wire = builder.mul(left_wire, right_wire);

        Ok(AllocatedBit {
            wire,
            value: result_value,
        })
    }
}

pub fn u64_into_boolean_vec_le(
    builder: &mut BuilderExt,
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
        .map(|b| Ok(Boolean::from(AllocatedBit::alloc(builder, b)?)))
        .collect::<Result<Vec<_>>>()?;

    Ok(bits)
}

pub fn field_into_boolean_vec_le<Scalar: PrimeField>(
    builder: &mut BuilderExt,
    value: Option<Scalar>,
) -> Result<Vec<Boolean>> {
    let v = field_into_allocated_bits_le::<Scalar>(builder, value)?;

    Ok(v.into_iter().map(Boolean::from).collect())
}

pub fn field_into_allocated_bits_le<Scalar: PrimeField>(
    builder: &mut BuilderExt,
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
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(builder, b))
        .collect::<Result<Vec<_>>>()?;

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
    pub fn wire(&self, b: &BuilderExt) -> WireId {
        match self {
            Boolean::Is(bit) => bit.wire,
            Boolean::Not(bit) => unimplemented!("Negated view of a bit"),
            Boolean::Constant(false) => b.zero,
            Boolean::Constant(true) => b.one,
        }
    }

    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false,
        }
    }

    pub fn enforce_equal<'l>(builder: &mut BuilderExt, a: &'l Self, b: &'l Self) -> Result<()> {
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
                        let w = AllocatedBit::not(builder, v);
                        builder.assert_zero(w.get_wire());
                    }
                    Boolean::Not(ref v) => {
                        builder.assert_zero(v.get_wire());
                    }
                    _ => { /* This case will never happen => DO NOTHING */ }
                }
                Ok(())
            }

            (&Boolean::Constant(false), c) | (c, &Boolean::Constant(false)) => {
                match &c {
                    Boolean::Is(ref v) => {
                        builder.assert_zero(v.get_wire());
                    }
                    Boolean::Not(ref v) => {
                        let w = AllocatedBit::not(builder, v);
                        builder.assert_zero(w.wire);
                    }
                    _ => { /* This case will never happen => DO NOTHING */ }
                }
                Ok(())
            }

            (&Boolean::Is(ref v), &Boolean::Is(ref w))
            | (&Boolean::Not(ref v), &Boolean::Not(ref w)) => {
                let xorwire = AllocatedBit::xor(builder, &v, &w)?.get_wire();
                builder.assert_zero(xorwire);

                Ok(())
            }

            (&Boolean::Is(ref v), &Boolean::Not(ref w))
            | (&Boolean::Not(ref v), &Boolean::Is(ref w)) => {
                let true_bit = AllocatedBit {
                    wire: builder.one,
                    value: Some(true),
                };
                let not_w = AllocatedBit::xor(builder, &w, &true_bit)?;
                let xor_wire = AllocatedBit::xor(builder, &v, &not_w)?.get_wire();
                builder.assert_zero(xor_wire);

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
    pub fn xor<'a>(builder: &mut BuilderExt, a: &'a Self, b: &'a Self) -> Result<Self> {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_))
            | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Ok(Boolean::xor(builder, is, &not.not())?.not())
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b))
            | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::xor(builder, a, b)?))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a>(builder: &mut BuilderExt, a: &'a Self, b: &'a Self) -> Result<Self> {
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
                Ok(Boolean::Is(AllocatedBit::and_not(builder, is, not)?))
            }
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::nor(builder, a, b)?))
            }
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::and(builder, a, b)?))
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

    use super::{field_into_allocated_bits_le, u64_into_boolean_vec_le, AllocatedBit, Boolean};

    use zki_sieve::producers::builder::{new_example_builder, Builder};
    use zki_sieve::producers::examples::*;
    use zki_sieve::{consumers::evaluator::Evaluator, Source};
    use zki_sieve::{Message, Relation};

    use crate::back::sieve_ir::builder_ext::BuilderExt;
    use crate::back::sieve_ir::field::{encode_scalar, QuarkScalar};
    use crate::back::sieve_ir::num::{scalar_from_biguint, scalar_from_unsigned};
    use ff::{Field, PrimeField};
    use num_bigint::BigUint;
    use num_traits::{Num, One, Zero};
    use std::ops::Neg;

    fn new_builder() -> BuilderExt {
        BuilderExt::new::<QuarkScalar>(new_example_builder())
    }

    fn evaluate(b: BuilderExt) -> Evaluator {
        let sink = b.finish();
        let source = Source::from_buffers(vec![
            sink.instance_buffer,
            sink.witness_buffer,
            sink.relation_buffer,
        ]);

        let mut evaluator = Evaluator::default();
        source
            .iter_messages()
            .for_each(|msg| evaluator.ingest_message(&msg.unwrap()));
        evaluator
    }

    macro_rules! initialize_everything {
        ($one_:ident, $zero_:ident, $neg_one:ident, $modulus:ident, $header:ident) => {
            let $one_ = BigUint::one();
            let $zero_ = BigUint::zero();
            let $neg_one: QuarkScalar = QuarkScalar::one().neg();
            let $modulus =
                BigUint::from_bytes_le(encode_scalar(&$neg_one).as_slice()) + BigUint::one();
            let $header = example_header_in_field($modulus.to_bytes_le());
        };
    }

    #[test]
    fn test_bit_allocated_bit() {
        initialize_everything!(one_, zero_, neg_one, modulus, header);

        let mut builder = new_builder();

        let v = AllocatedBit::alloc(&mut builder, Some(true)).unwrap();
        assert_eq!(v.get_value(), Some(true));

        let w = AllocatedBit::alloc(&mut builder, Some(false)).unwrap();
        assert_eq!(w.get_value(), Some(false));

        let evaluator = evaluate(builder);

        assert_eq!(evaluator.get(v.get_wire()).unwrap(), &one_);
        assert_eq!(evaluator.get(w.get_wire()).unwrap(), &zero_);
    }

    #[test]
    fn test_bit_xor() {
        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut builder = new_builder();
                let a = AllocatedBit::alloc(&mut builder, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut builder, Some(*b_val)).unwrap();
                let c = AllocatedBit::xor(&mut builder, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val ^ *b_val);

                let evaluator = evaluate(builder);
                assert_eq!(
                    evaluator.get(a.get_wire()).unwrap(),
                    if *a_val { &one_ } else { &zero_ }
                );
                assert_eq!(
                    evaluator.get(b.get_wire()).unwrap(),
                    if *b_val { &one_ } else { &zero_ }
                );

                assert_eq!(
                    evaluator.get(c.get_wire()).unwrap(),
                    if c.value.unwrap() { &one_ } else { &zero_ }
                );

                assert_eq!(evaluator.get_violations().len(), 0 as usize);
            }
        }
    }

    #[test]
    fn test_bit_and() {
        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut builder = new_builder();
                let a = AllocatedBit::alloc(&mut builder, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut builder, Some(*b_val)).unwrap();
                let c = AllocatedBit::and(&mut builder, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & *b_val);

                let evaluator = evaluate(builder);
                assert_eq!(
                    evaluator.get(a.get_wire()).unwrap(),
                    if *a_val { &one_ } else { &zero_ }
                );
                assert_eq!(
                    evaluator.get(b.get_wire()).unwrap(),
                    if *b_val { &one_ } else { &zero_ }
                );

                assert_eq!(
                    evaluator.get(c.get_wire()).unwrap(),
                    if c.value.unwrap() { &one_ } else { &zero_ }
                );

                assert_eq!(evaluator.get_violations().len(), 0 as usize);
            }
        }
    }

    #[test]
    fn test_bit_and_not() {
        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut builder = new_builder();
                let a = AllocatedBit::alloc(&mut builder, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut builder, Some(*b_val)).unwrap();
                let c = AllocatedBit::and_not(&mut builder, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & !*b_val);

                let evaluator = evaluate(builder);
                assert_eq!(
                    evaluator.get(a.get_wire()).unwrap(),
                    if *a_val { &one_ } else { &zero_ }
                );
                assert_eq!(
                    evaluator.get(b.get_wire()).unwrap(),
                    if *b_val { &one_ } else { &zero_ }
                );

                assert_eq!(
                    evaluator.get(c.get_wire()).unwrap(),
                    if c.value.unwrap() { &one_ } else { &zero_ }
                );

                assert_eq!(evaluator.get_violations().len(), 0 as usize);
            }
        }
    }

    #[test]
    fn test_bit_nor() {
        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut builder = new_builder();
                let a = AllocatedBit::alloc(&mut builder, Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(&mut builder, Some(*b_val)).unwrap();
                let c = AllocatedBit::nor(&mut builder, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !*a_val & !*b_val);

                let evaluator = evaluate(builder);
                assert_eq!(
                    evaluator.get(a.get_wire()).unwrap(),
                    if *a_val { &one_ } else { &zero_ }
                );
                assert_eq!(
                    evaluator.get(b.get_wire()).unwrap(),
                    if *b_val { &one_ } else { &zero_ }
                );

                assert_eq!(
                    evaluator.get(c.get_wire()).unwrap(),
                    if c.value.unwrap() { &one_ } else { &zero_ }
                );

                assert_eq!(evaluator.get_violations().len(), 0);
            }
        }
    }

    #[test]
    fn test_boolean_enforce_equal() {
        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        {
                            let mut builder = new_builder();

                            let mut a = Boolean::from(
                                AllocatedBit::alloc(&mut builder, Some(a_bool)).unwrap(),
                            );
                            let mut b = Boolean::from(
                                AllocatedBit::alloc(&mut builder, Some(b_bool)).unwrap(),
                            );

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
                            let mut b = Boolean::from(
                                AllocatedBit::alloc(&mut builder, Some(b_bool)).unwrap(),
                            );

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

                            let mut a = Boolean::from(
                                AllocatedBit::alloc(&mut builder, Some(a_bool)).unwrap(),
                            );
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

        let mut b = Boolean::from(AllocatedBit::alloc(&mut builder, Some(true)).unwrap());

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

        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut builder = new_builder();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| match operand {
                        OperandType::True => Boolean::constant(true),
                        OperandType::False => Boolean::constant(false),
                        OperandType::AllocatedTrue => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(true)).unwrap())
                        }
                        OperandType::AllocatedFalse => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(false)).unwrap())
                        }
                        OperandType::NegatedAllocatedTrue => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(true)).unwrap())
                                .not()
                        }
                        OperandType::NegatedAllocatedFalse => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(false)).unwrap())
                                .not()
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::xor(&mut builder, &a, &b).unwrap();
                let c_wire = c.wire(&builder);

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
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
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

        initialize_everything!(one_, zero_, neg_one, modulus, header);

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut builder = new_builder();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| match operand {
                        OperandType::True => Boolean::constant(true),
                        OperandType::False => Boolean::constant(false),
                        OperandType::AllocatedTrue => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(true)).unwrap())
                        }
                        OperandType::AllocatedFalse => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(false)).unwrap())
                        }
                        OperandType::NegatedAllocatedTrue => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(true)).unwrap())
                                .not()
                        }
                        OperandType::NegatedAllocatedFalse => {
                            Boolean::from(AllocatedBit::alloc(&mut builder, Some(false)).unwrap())
                                .not()
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::and(&mut builder, &a, &b).unwrap();
                let c_wire = c.wire(&builder);

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
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
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
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
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
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
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
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &zero_);
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert_eq!(evaluator.get(c_wire).unwrap(), &one_);
                        assert_eq!(v.value, Some(true));
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
        initialize_everything!(one_, zero_, neg_one, modulus, header);
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
        initialize_everything!(one_, zero_, neg_one, modulus, header);
        let mut builder = new_builder();

        let r = QuarkScalar::from_str("139407991430939255523467833655006660152").unwrap();

        let bits = field_into_allocated_bits_le(&mut builder, Some(r)).unwrap();

        let evaluator = evaluate(builder);
        assert_eq!(evaluator.get_violations().len(), 0);

        assert_eq!(bits.len(), 128);

        assert_eq!(bits[127 - 4].value.unwrap(), true);
        assert_eq!(bits[127 - 7].value.unwrap(), false);
        assert_eq!(bits[127 - 16].value.unwrap(), false);
        assert_eq!(bits[127 - 20].value.unwrap(), false);
        assert_eq!(bits[127 - 29].value.unwrap(), true);
        assert_eq!(bits[127 - 37].value.unwrap(), false);
        assert_eq!(bits[127 - 47].value.unwrap(), true);
        assert_eq!(bits[127 - 60].value.unwrap(), false);
        assert_eq!(bits[127 - 74].value.unwrap(), false);
    }
}
