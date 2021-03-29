// Inspired from bellman::gadgets::boolean

use zki_sieve::Sink;
use zki_sieve::{Result, WireId};

use crate::back::sieve_ir::ir_builder::IRBuilder;

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

    pub fn alloc(b: &mut IRBuilder<impl Sink>, value: Option<bool>) -> Result<Self> {
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
    pub fn not(b: &mut IRBuilder<impl Sink>, a: &Self) -> Self {
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
    pub fn xor(builder: &mut IRBuilder<impl Sink>, a: &Self, b: &Self) -> Result<Self> {
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
    pub fn and(builder: &mut IRBuilder<impl Sink>, a: &Self, b: &Self) -> Result<Self> {
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
    pub fn and_not(builder: &mut IRBuilder<impl Sink>, a: &Self, b: &Self) -> Result<Self> {
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
    pub fn nor(builder: &mut IRBuilder<impl Sink>, a: &Self, b: &Self) -> Result<Self> {
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
    pub fn wire(&self, b: &IRBuilder<impl Sink>) -> WireId {
        match self {
            Boolean::Is(bit) => bit.wire,
            Boolean::Not(_bit) => unimplemented!("Negated view of a bit"),
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

    pub fn enforce_equal<'l>(
        builder: &mut IRBuilder<impl Sink>,
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
    pub fn xor<'a>(builder: &mut IRBuilder<impl Sink>, a: &'a Self, b: &'a Self) -> Result<Self> {
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
    pub fn and<'a>(builder: &mut IRBuilder<impl Sink>, a: &'a Self, b: &'a Self) -> Result<Self> {
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
