use std::ops::{Add, Sub, Mul};
use std::cmp::max;

#[derive(Copy, Clone)]
pub enum BitWidth {
    Unknown,
    Max(usize),
}

use BitWidth::*;

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