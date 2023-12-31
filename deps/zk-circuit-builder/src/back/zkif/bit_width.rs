use std::ops::{Add, Sub, Mul};
use std::cmp::max;
use num_bigint::{BigUint, BigInt, Sign};
use zkinterface_bellman::bellman::gadgets::boolean::Boolean;
use crate::back::zkif::int::Int;

#[derive(Copy, Clone, Debug)]
pub enum BitWidth {
    Unknown,
    Max(/* width */ usize, /* signed */ bool),
}

use BitWidth::*;

impl BitWidth {
    pub fn zero() -> Self {
        Max(0, false)
    }
}

impl From<u64> for BitWidth {
    fn from(literal: u64) -> Self {
        Max(64 - literal.leading_zeros() as usize, false)
    }
}

impl From<i64> for BitWidth {
    fn from(literal: i64) -> Self {
        if literal >= 0 {
            BitWidth::from(literal as u64)
        } else {
            Self::zero() - BitWidth::from((-literal) as u64)
        }
    }
}

impl From<&BigUint> for BitWidth {
    fn from(literal: &BigUint) -> Self {
        Max(literal.bits() as usize, false)
    }
}

impl From<&BigInt> for BitWidth {
    fn from(literal: &BigInt) -> Self {
        let (sign, mag) = literal.clone().into_parts();
        match sign {
            Sign::Minus => Self::zero() - BitWidth::from(&mag),
            Sign::Plus | Sign::NoSign => BitWidth::from(&mag),
        }
    }
}

impl From<&Boolean> for BitWidth {
    /// This is a type-safe way to show that we have a validated boolean.
    fn from(_: &Boolean) -> Self {
        Max(1, false)
    }
}

impl From<&Int> for BitWidth {
    /// This is a type-safe way to show that we have a validated integer.
    fn from(_: &Int) -> Self {
        Max(32, false)
    }
}

impl Add<Self> for BitWidth {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self, other) {
            // x + 0 = x
            (Max(_, _), Max(0, _)) => self,
            (Max(0, _), Max(_, _)) => other,
            // x + y = add one bit, propagate signed-ness
            (Max(w1, s1), Max(w2, s2)) => Max(
                max(w1, w2) + 1,
                s1 || s2),
            _ => Unknown,
        }
    }
}

impl Sub<Self> for BitWidth {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match (self, other) {
            // x - 0 = x.
            (Max(_, _), Max(0, _)) => self,
            // 0 - x = x, always signed.
            (Max(0, _), Max(w, _)) => Max(w, true),
            // x - y = add one bit, always signed.
            (Max(w1, _), Max(w2, _)) => Max(
                max(w1, w2) + 1,
                true),
            _ => Unknown,
        }
    }
}

impl Mul<Self> for BitWidth {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match (self, other) {
            // x * 1 = same width, propagate signed-ness.
            (Max(w, s1), Max(1, s2)) => Max(
                w, s1 || s2),
            (Max(1, s1), Max(w, s2)) => Max(
                w, s1 || s2),
            // x * y = accumulate widths, propagate signed-ness.
            (Max(w1, s1), Max(w2, s2)) => Max(
                w1 + w2,
                s1 || s2),
            _ => Unknown,
        }
    }
}
