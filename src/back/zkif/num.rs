use zkinterface_bellman::{
    ff::{ScalarEngine, Field},
    bellman::LinearCombination,
};
use std::ops::{Add, Sub, Mul};
use zkinterface_bellman::bellman::{ConstraintSystem, SynthesisError, Variable};
use zkinterface_bellman::sapling_crypto::circuit::boolean::Boolean;


#[derive(Clone)]
pub struct Num<E: ScalarEngine> {
    pub value: Option<E::Fr>,
    pub lc: LinearCombination<E>,
}

impl<E: ScalarEngine> Num<E> {
    pub fn zero() -> Self {
        Num {
            value: Some(E::Fr::zero()),
            lc: LinearCombination::zero(),
        }
    }

    pub fn from_boolean<CS: ConstraintSystem<E>>(
        bool: &Boolean,
        cs: &CS,
    ) -> Self {
        Num {
            value: bool.get_value().map(|b|
                if b { E::Fr::one() } else { E::Fr::zero() }
            ),
            lc: boolean_lc(bool, CS::one(), E::Fr::one()),
        }
    }

    pub fn mul(mut self, other: &Self,
               cs: &mut impl ConstraintSystem<E>,
    ) -> Self {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.mul_assign(other_val),

            _ => {}
        }

        let product = cs.alloc(
            || "product",
            || self.value.ok_or(SynthesisError::AssignmentMissing),
        ).unwrap();
        let product_lc = LinearCombination::<E>::zero() + product;

        cs.enforce(
            || "multiplication",
            |lc| lc + &self.lc,
            |lc| lc + &other.lc,
            |lc| lc + &product_lc,
        );

        self.lc = product_lc;
        self
    }
}

impl<'a, E: ScalarEngine> Add<&'a Num<E>> for Num<E> {
    type Output = Num<E>;

    fn add(mut self, other: &'a Num<E>) -> Num<E> {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.add_assign(other_val),

            _ => {}
        }

        self.lc = self.lc + &other.lc;
        self
    }
}

impl<'a, E: ScalarEngine> Sub<&'a Num<E>> for Num<E> {
    type Output = Num<E>;

    fn sub(mut self, other: &'a Num<E>) -> Num<E> {
        match (&mut self.value, &other.value) {
            (
                Some(ref mut self_val),
                Some(ref other_val)
            ) => self_val.sub_assign(other_val),

            _ => {}
        }

        self.lc = self.lc - &other.lc;
        self
    }
}


// Copy of Boolean::lc, but using ScalarEngine instead of Engine.
pub fn boolean_lc<E: ScalarEngine>(
    bool: &Boolean,
    one: Variable,
    coeff: E::Fr,
) -> LinearCombination<E>
{
    match bool {
        &Boolean::Constant(c) => {
            if c {
                LinearCombination::<E>::zero() + (coeff, one)
            } else {
                LinearCombination::<E>::zero()
            }
        }
        &Boolean::Is(ref v) => {
            LinearCombination::<E>::zero() + (coeff, v.get_variable())
        }
        &Boolean::Not(ref v) => {
            LinearCombination::<E>::zero() + (coeff, one) - (coeff, v.get_variable())
        }
    }
}