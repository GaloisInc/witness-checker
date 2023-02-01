// Inspired from bellman::gadgets::boolean

use zki_sieve_v3::Result;

use crate::back::sieve_ir_v2::ir_builder::{IRBuilderT, IRWire};

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone)]
pub struct AllocatedBit {
    wire: IRWire,
    value: Option<bool>,
}

impl AllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_wire(&self) -> &IRWire {
        &self.wire
    }

    pub fn alloc(b: &mut impl IRBuilderT, value: Option<bool>) -> Self {
        let field_value = match value {
            Some(false) => Some(vec![0]),
            Some(true) => Some(vec![1]),
            None => None,
        };
        let wire = b.new_witness(field_value);

        // (x - 1) * x == 0

        // This `sub1` may underflow if `wire` is 0, but this is harmless as we only care whether
        // `wire_1` is zero or nonzero.
        let wire_1 = b.sub1(&wire);
        let prod = b.mul(&wire, &wire_1);
        b.assert_zero(&prod);

        AllocatedBit { wire, value }
    }

    /// Calculates `NOT a`.
    pub fn not(b: &mut impl IRBuilderT, a: &Self) -> Self {
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
        let wire = b.sub(&b.one(), a.get_wire());

        AllocatedBit { wire, value }
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor(builder: &mut impl IRBuilderT, a: &Self, b: &Self) -> Self {
        let value = match (a.value, b.value) {
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

        // This `sub` may underflow to -1 if `a` is 0 and `b` is 1.  But `-1 * -1 == 1` regardless
        // of the choice of modulus, so this is okay.
        let tmp_wire = builder.sub(a.get_wire(), b.get_wire());
        let wire = builder.mul(&tmp_wire, &tmp_wire);

        AllocatedBit { wire, value }
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and(builder: &mut impl IRBuilderT, a: &Self, b: &Self) -> Self {
        let value = match (a.value, b.value) {
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

        AllocatedBit { wire, value }
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not(builder: &mut impl IRBuilderT, a: &Self, b: &Self) -> Self {
        let value = match (a.value, b.value) {
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
        let right_wire = builder.sub(&builder.one(), b.get_wire());
        let wire = builder.mul(a.get_wire(), &right_wire);

        AllocatedBit { wire, value }
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor(builder: &mut impl IRBuilderT, a: &Self, b: &Self) -> Self {
        let value = match (a.value, b.value) {
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
        let left_wire = builder.sub(&builder.one(), a.get_wire());
        let right_wire = builder.sub(&builder.one(), b.get_wire());
        let wire = builder.mul(&left_wire, &right_wire);

        AllocatedBit { wire, value }
    }
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
    pub fn alloc(b: &mut impl IRBuilderT, value: Option<bool>) -> Self {
        Boolean::Is(AllocatedBit::alloc(b, value))
    }

    pub fn wire(&self, b: &mut impl IRBuilderT) -> IRWire {
        match self {
            Boolean::Is(bit) => bit.wire.clone(),
            Boolean::Not(bit) => AllocatedBit::not(b, bit).get_wire().clone(),
            Boolean::Constant(false) => b.zero(),
            Boolean::Constant(true) => b.one(),
        }
    }

    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false,
        }
    }

    pub fn enforce_true(&self, builder: &mut impl IRBuilderT) -> Result<()> {
        Self::enforce_equal(builder, self, &Boolean::Constant(true))
    }

    pub fn enforce_equal<'l>(
        builder: &mut impl IRBuilderT,
        a: &'l Self,
        b: &'l Self,
    ) -> Result<()> {
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
                    _ => unreachable!(),
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
                        builder.assert_zero(w.get_wire());
                    }
                    _ => unreachable!(),
                }
                Ok(())
            }

            (&Boolean::Is(ref v), &Boolean::Is(ref w))
            | (&Boolean::Not(ref v), &Boolean::Not(ref w)) => {
                let xorwire = AllocatedBit::xor(builder, &v, &w).get_wire().clone();
                builder.assert_zero(&xorwire);

                Ok(())
            }

            (&Boolean::Is(ref v), &Boolean::Not(ref w))
            | (&Boolean::Not(ref v), &Boolean::Is(ref w)) => {
                let true_bit = AllocatedBit {
                    wire: builder.one(),
                    value: Some(true),
                };
                let not_w = AllocatedBit::xor(builder, &w, &true_bit);
                let xor_wire = AllocatedBit::xor(builder, &v, &not_w).get_wire().clone();
                builder.assert_zero(&xor_wire);

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
    pub fn xor<'a>(builder: &mut impl IRBuilderT, a: &'a Self, b: &'a Self) -> Self {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => x.clone(),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => x.not(),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_))
            | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Boolean::xor(builder, is, &not.not()).not()
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b))
            | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Boolean::Is(AllocatedBit::xor(builder, a, b))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a>(builder: &mut impl IRBuilderT, a: &'a Self, b: &'a Self) -> Self {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => {
                Boolean::Constant(false)
            }
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => x.clone(),
            // a AND (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not))
            | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Boolean::Is(AllocatedBit::and_not(builder, is, not))
            }
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Boolean::Is(AllocatedBit::nor(builder, a, b))
            }
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Boolean::Is(AllocatedBit::and(builder, a, b))
            }
        }
    }
}

impl From<AllocatedBit> for Boolean {
    fn from(b: AllocatedBit) -> Boolean {
        Boolean::Is(b)
    }
}
