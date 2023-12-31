// Based on
//     https://github.com/zcash/librustzcash/tree/d7ba3102/
// License MIT
// Copyright (c) 2017-2019 Electric Coin Company

use ff::PrimeField;
use num_bigint::BigUint;
use std::cmp;

use super::{
    boolean::Boolean,
    field::{encode_scalar, scalar_from_biguint},
    int::Int,
    ir_builder::IRBuilderT,
};
use crate::back::sieve_ir_v2::ir_builder::IRWire;

/// A number, represented as a single field element.
#[derive(Clone)]
pub struct Num<Scalar: PrimeField> {
    pub value: Option<Scalar>,
    pub zki_wire: IRWire,

    /// Conservative upper bound on the number of bits required to represent this number.
    /// Specifically, the `Scalar` value is always less than `2^real_bits`.  `real_bits` may exceed
    /// `logical_bits`, but can't exceed the size of the field.
    pub real_bits: u16,

    /// The number of bits containing meaningful values.  Bits in the range `valid_bits ..
    /// real_bits` may contain arbitrary data.
    pub valid_bits: u16,
}

impl<Scalar: PrimeField> Num<Scalar> {
    pub fn from_biguint(b: &mut impl IRBuilderT, width: u16, value: &BigUint) -> Num<Scalar> {
        let element: Scalar = scalar_from_biguint(value).unwrap();
        let zki_wire = b.new_constant(encode_scalar(&element));

        Num {
            value: Some(element),
            zki_wire,
            real_bits: width,
            valid_bits: width,
        }
    }

    pub fn from_int(builder: &mut impl IRBuilderT, int: &Int) -> Num<Scalar> {
        let value = int.value.as_ref().map(|x| scalar_from_biguint(x).unwrap());
        let zki_wire = Self::compose_bits(builder, &int.bits);
        let width = int.width() as u16;

        Num {
            value,
            zki_wire,
            real_bits: width,
            valid_bits: width,
        }
    }

    fn compose_bits(b: &mut impl IRBuilderT, bits: &[Boolean]) -> IRWire {
        if bits.len() == 0 {
            return b.zero();
        }

        bits.iter()
            .enumerate()
            .skip(1)
            .fold(bits[0].wire(b), |sum, (exponent, bit)| {
                let coeff = b.power_of_two(exponent);
                let bit_wire = bit.wire(b);
                let term = b.mulc(&bit_wire, coeff);
                let res = b.add(&sum, &term);
                res
            })
    }

    /// Decompose this number into bits, least-significant first.  Returns `self.real_bits` bits.
    pub fn to_bits(&self, b: &mut impl IRBuilderT) -> Vec<Boolean> {
        b.annotate("to_bits");

        let n_bits = self.real_bits as usize;

        let values: Vec<Option<bool>> = match &self.value {
            Some(val) => {
                let bits = val.to_le_bits();
                bits.iter().take(n_bits).map(|b| Some(*b)).collect()
            }
            None => vec![None; n_bits],
        };

        let bits: Vec<Boolean> = values
            .into_iter()
            .map(|value| Boolean::alloc(b, value))
            .collect();

        // Enforce that the bit representation is equivalent to this Num.
        let recomposed_wire = Self::compose_bits(b, &bits);
        // This `sub` may underflow, but we only care whether the result is zero or nonzero.
        let difference = b.sub(&self.zki_wire, &recomposed_wire);
        b.assert_zero(&difference);

        b.deannotate();
        bits
    }

    // TODO: Turn add/sub/mul/neg into wrappers that check for the necessary width and truncate the
    // inputs to `cmp::min(self.real_bits, other.real_bits)` if needed.

    pub fn add_assign(
        mut self,
        other: &Self,
        builder: &mut impl IRBuilderT,
    ) -> Result<Self, String> {
        let new_real_bits = cmp::max(self.real_bits, other.real_bits) + 1;
        if new_real_bits > Scalar::CAPACITY as u16 {
            return Err(format!(
                "sum of {} bits and {} bits doesn't fit in a field element ({} usable bits)",
                self.real_bits,
                other.real_bits,
                Scalar::CAPACITY,
            ));
        }

        match (&mut self.value, &other.value) {
            (Some(ref mut self_val), Some(ref other_val)) => self_val.add_assign(other_val),
            _ => {}
        }

        self.zki_wire = builder.add(&self.zki_wire, &other.zki_wire);

        self.real_bits = new_real_bits;
        self.valid_bits = cmp::min(self.valid_bits, other.valid_bits);
        Ok(self)
    }

    pub fn sub(mut self, other: &Self, b: &mut impl IRBuilderT) -> Result<Self, String> {
        // `a - b` might underflow in the field, producing garbage.  We compute `a + (2^N - b)`
        // instead, with `N` large enough that `2^N - b` can't underflow.  This makes `a.sub(b)`
        // essentially equivalent to `a.add(b.neg())`, except it saves a bit.  `2^N - b` is at most
        // `2^N`, and the sum `a + 2^N` is at most `1 + max(a_bits, N)` bits, so `sub` adds 1 bit
        // to the size of its inputs.  But `neg` and `add` would each add 1, for a total of 2.
        //
        // Note we don't need to consult `self.real_bits` here.  If `self.real_bits >
        // other.real_bits`, then we'll trample on some high bits of `self`, but that's okay
        // because `valid_bits` is the `min` of the two inputs, and will be smaller than
        // `other.real_bits`.

        let new_real_bits = cmp::max(self.real_bits, other.real_bits) + 1;
        if new_real_bits > Scalar::CAPACITY as u16 {
            return Err(format!(
                "sum of {} bits and {} bits doesn't fit in a field element ({} usable bits)",
                self.real_bits,
                other.real_bits,
                Scalar::CAPACITY,
            ));
        }

        let max_value: Scalar = scalar_from_biguint(&(BigUint::from(1_u8) << other.real_bits))?;

        match (&mut self.value, &other.value) {
            (Some(ref mut self_val), Some(ref other_val)) => {
                self_val.add_assign(max_value - other_val)
            }
            _ => {}
        }

        // Compute max_value + other * -1 + self
        // TODO: cache max_wire.
        let max_wire = b.new_constant(encode_scalar(&max_value));
        let other_shifted = b.sub(&max_wire, &other.zki_wire);
        self.zki_wire = b.add(&self.zki_wire, &other_shifted);

        self.real_bits = new_real_bits;
        self.valid_bits = cmp::min(self.valid_bits, other.valid_bits);

        Ok(self)
    }

    pub fn mul(mut self, other: &Self, b: &mut impl IRBuilderT) -> Result<Self, String> {
        fn mul_bits(b1: u16, b2: u16) -> u16 {
            // If `bits == 0`, then the value must be zero, so the product is also zero.
            if b1 == 0 || b2 == 0 {
                0
            }
            // If `bits == 1`, then the value must be 0 or 1.  The product can either be zero or
            // the value of the other input.
            else if b1 == 1 {
                b2
            } else if b2 == 1 {
                b1
            } else {
                b1 + b2
            }
        }
        let new_real_bits = mul_bits(self.real_bits, other.real_bits);
        // NB: This is the one case where `real_bits` is allowed to exactly equal the number of
        // bits in a field element.  The inputs can't exceed `2^b1 - 1` and `2^b2 - 1`, so the
        // product will be less than `2^(b1 + b2)` by at least `2^b1 + 2^b2`; in the worst case
        // (`b1 = b2 = NUM_BITS / 2`), this is a fairly large number, like `2^64`.  We assume the
        // prime modulus is much closer to `2^NUM_BITS` than that, so the product will fit.
        // The prime modulus must be `>= 2^NUM_BITS - 2^(NUM_BITS/2)`, see test_backend_scalar().
        if new_real_bits > Scalar::NUM_BITS as u16 {
            return Err(format!(
                "product of {} bits and {} bits doesn't fit in a field element ({} bits)",
                self.real_bits,
                other.real_bits,
                Scalar::NUM_BITS,
            ));
        }

        match (&mut self.value, &other.value) {
            (Some(ref mut self_val), Some(ref other_val)) => self_val.mul_assign(other_val),
            _ => {}
        }

        self.zki_wire = b.mul(&self.zki_wire, &other.zki_wire);

        self.real_bits = new_real_bits;

        self.valid_bits = cmp::min(self.real_bits, other.real_bits);
        assert!(self.valid_bits <= self.real_bits);

        Ok(self)
    }

    pub fn neg(mut self, b: &mut impl IRBuilderT) -> Result<Self, String> {
        // Computing `0 - a` in the field could underflow, producing garbage.  We instead compute
        // `2^N - a`, which never underflows, but does increase `real_bits` by one.

        let new_real_bits = self.real_bits + 1;
        if new_real_bits > Scalar::CAPACITY as u16 {
            return Err(format!(
                "negation of {} bits doesn't fit in a field element ({} bits)",
                self.real_bits,
                Scalar::CAPACITY,
            ));
        }

        let max_value: Scalar =
            scalar_from_biguint::<Scalar>(&(BigUint::from(1_u8) << self.real_bits))?;

        self.value = match self.value {
            Some(val) => Some(max_value - val),
            None => None,
        };

        // Compute max_value + self * -1
        // TODO: cache max_wire.
        let max_wire = b.new_constant(encode_scalar(&max_value));
        self.zki_wire = b.sub(&max_wire, &self.zki_wire);

        self.real_bits = new_real_bits;
        // `valid_bits` remains the same.

        Ok(self)
    }

    pub fn mux(
        mut self,
        else_: &Self,
        cond: &Self,
        b: &mut impl IRBuilderT,
    ) -> Result<Self, String> {
        if cond.real_bits == 0 || cond.valid_bits == 0 {
            // This probably won't ever happen, but if it does, we know the logical value of
            // `condition` must be zero.
            return Ok(else_.clone());
        }
        if cond.real_bits != 1 || cond.valid_bits != 1 {
            return Err(format!(
                "mux requires a truncated boolean, but got {} real bits",
                cond.real_bits,
            ));
        }

        // `Some(true)` if the mux selects the `self` branch, `Some(false)` for `else_`, `None`
        // for unknown.
        // TODO: make constant time w.r.t. condition.
        let select = cond.value.as_ref().map(|x| !x.is_zero());
        self.value = match select {
            Some(true) => self.value.clone(),
            Some(false) => else_.value.clone(),
            None => None,
        };

        // result = cond * (self - else) + else
        // This computation is field size agnostic: some steps may overflow the `Scalar` modulus or
        // any higher modulus, without affecting the result.
        let self_else = b.sub(&self.zki_wire, &else_.zki_wire);
        let cond_self_else = b.mul(&self_else, &cond.zki_wire);
        self.zki_wire = b.add(&cond_self_else, &else_.zki_wire);

        // We know from the check above that `self` has `real_bits == 1`, meaning its value is
        // either 0 or 1.  This means the result is either exactly `then_` or exactly `else_`, and
        // there's no need to increment `real_bits`.
        self.real_bits = cmp::max(self.real_bits, else_.real_bits);
        self.valid_bits = cmp::min(self.valid_bits, else_.valid_bits);

        Ok(self)
    }

    /// is_truncated means that the range of values of this Num is exactly the valid range.
    pub fn is_truncated(&self) -> bool {
        return self.real_bits == self.valid_bits;
    }

    /// Truncate `self` modulo `2^valid_bits`, producing a new `Num` with `real_bits ==
    /// valid_bits`.
    /// Note: WireRepr.as_num_trunc is better for this, because it caches the Int representation.
    // TODO: simple take the right wire in the bit recomposition (like `compose_bits`).
    fn _truncate(self, b: &mut impl IRBuilderT) -> Self {
        if self.real_bits == self.valid_bits {
            return self;
        }

        let int = Int::from_num(b, self.valid_bits as usize, &self);
        Self::from_int(b, &int)
    }

    pub fn equals_zero(&self, b: &mut impl IRBuilderT) -> Boolean {
        let is_zero_bool = {
            let value = self.value.map(|val| val.is_zero());
            Boolean::alloc(b, value)
        };
        // TODO: the boolean constraint of AllocatedBit should not be necessary
        // because the constraints below already enforce booleanness.

        // let num = self.zki_wire.clone();
        let is_zero = is_zero_bool.wire(b);

        b.check_is_zero(&self.zki_wire, &self.value, &is_zero);

        is_zero_bool
    }

    pub fn zero_extend(&self, new_width: u16) -> Result<Self, String> {
        assert!(new_width >= self.valid_bits);

        // It's only safe to extend if we know all high bits are zero.
        if self.real_bits > self.valid_bits {
            return Err(format!(
                "zero_extend requires a truncated input, \
                    but real_bits ({}) exceeds valid_bits ({})",
                self.real_bits, self.valid_bits,
            ));
        }

        let mut extended = self.clone();
        // TODO: once we remove the `real_bits >= valid_bits` invariant, we won't need to adjust
        // `real_bits` here.
        extended.real_bits = new_width;
        extended.valid_bits = new_width;
        Ok(extended)
    }
}
