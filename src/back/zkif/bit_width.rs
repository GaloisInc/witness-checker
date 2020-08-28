use std::ops::{Add, Sub, Mul};
use std::cmp::max;
use zkinterface_bellman::sapling_crypto::circuit::{boolean::Boolean};
use crate::back::zkif::uint32::UInt32;

#[derive(Copy, Clone, Debug)]
pub enum BitWidth {
    Unknown,
    Max(usize),
}

use BitWidth::*;

impl BitWidth {
    /// Whether this bit width would fit into a bit representation.
    pub fn fits_into(self, bit_capacity: usize) -> bool {
        match self {
            BitWidth::Unknown => false,
            BitWidth::Max(w) => w <= bit_capacity,
        }
    }
}

impl From<u64> for BitWidth {
    fn from(literal: u64) -> Self {
        Max(64 - literal.leading_zeros() as usize)
    }
}

impl From<i64> for BitWidth {
    fn from(literal: i64) -> Self {
        if literal >= 0 {
            BitWidth::from(literal as u64)
        } else {
            Max(0) - BitWidth::from((-literal) as u64)
        }
    }
}

impl From<&Boolean> for BitWidth {
    /// This is a type-safe way to show that we have a validated boolean.
    fn from(_: &Boolean) -> Self {
        Max(1)
    }
}

impl From<&UInt32> for BitWidth {
    /// This is a type-safe way to show that we have a validated integer.
    fn from(_: &UInt32) -> Self {
        Max(32)
    }
}

impl Add<Self> for BitWidth {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Max(s), Max(o)) => Max(
                max(s, o) + 1
            ),
            _ => Unknown,
        }
    }
}

impl Sub<Self> for BitWidth {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self + other
    }
}

impl Mul<Self> for BitWidth {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Max(s), Max(o)) => Max(
                s + o
            ),
            _ => Unknown,
        }
    }
}