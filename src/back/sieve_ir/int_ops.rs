use super::{boolean::Boolean, int::Int, ir_builder::IRBuilderT, num::Num};
use ff::PrimeField;
use num_traits::Zero;
use std::cmp;

pub fn bitwise_xor(builder: &mut impl IRBuilderT, left: &Int, right: &Int) -> Int {
    left.xor(builder, right)
}

// NICE-TO-HAVE: Implement directly on the Int type
pub fn bitwise_and(builder: &mut impl IRBuilderT, left: &Int, right: &Int) -> Int {
    let out_bits: Vec<Boolean> = left
        .bits
        .iter()
        .zip(right.bits.iter())
        .map(|(l, r)| Boolean::and(builder, l, r))
        .collect();

    Int::from_bits(&out_bits)
}

pub fn bitwise_or(builder: &mut impl IRBuilderT, left: &Int, right: &Int) -> Int {
    let out_bits: Vec<Boolean> = left
        .bits
        .iter()
        .zip(right.bits.iter())
        .map(|(l, r)| bool_or(builder, l, r))
        .collect();

    Int::from_bits(&out_bits)
}

pub fn bool_or<'a>(builder: &mut impl IRBuilderT, a: &'a Boolean, b: &'a Boolean) -> Boolean {
    Boolean::and(builder, &a.not(), &b.not()).not()
}

pub fn div<Scalar: PrimeField>(
    builder: &mut impl IRBuilderT,
    numer_num: &Num<Scalar>,
    numer_int: &Int,
    denom_num: &Num<Scalar>,
    denom_int: &Int,
) -> (
    /*quotient*/ Num<Scalar>,
    Int,
    /*rest*/ Num<Scalar>,
    Int,
) {
    builder.annotate("int_opts::div");

    let (quot_val, rest_val) = match (numer_int.value.as_ref(), denom_int.value.as_ref()) {
        (Some(numer), Some(denom)) => {
            if denom.is_zero() {
                (Some(0_u8.into()), Some(numer.clone()))
            } else {
                let quot_val = numer / denom;
                let rest_val = numer % denom;
                (Some(quot_val), Some(rest_val))
            }
        }
        _ => (None, None),
    };

    let max_width = cmp::max(numer_int.width(), denom_int.width());
    let quot_int = Int::alloc(builder, max_width, quot_val);
    let rest_int = Int::alloc(builder, denom_int.width(), rest_val);

    let quot_num = Num::from_int(builder, &quot_int);
    let rest_num = Num::from_int(builder, &rest_int);

    // Ensure that: numerator == quotient * denominator + rest.
    // we first compute 'quotient * denominator', then 'numerator - rest', finally compute the
    // difference of the two and ensure that it's null.
    let quo_times_denom = builder.mul(quot_num.zki_wire.clone(), denom_num.zki_wire.clone());
    let num_minus_rest = builder.sub(numer_num.zki_wire.clone(), rest_num.zki_wire.clone());
    let diff_all = builder.sub(quo_times_denom, num_minus_rest);
    builder.assert_zero(diff_all);

    // Verify that rest < denom || denom == 0.
    let width = denom_int.width();
    let diff_num = rest_num
        .zero_extend(width as u16 + 1)
        .unwrap()
        .sub(&denom_num.zero_extend(width as u16 + 1).unwrap(), builder)
        .unwrap();
    let diff_int = Int::from_num(builder, width + 1, &diff_num);
    let diff_ok = diff_int.is_negative();
    let denom_zero = denom_num.equals_zero(builder);
    let ok = bool_or(builder, &diff_ok, &denom_zero);

    ok.enforce_true(builder).unwrap();

    builder.deannotate();
    (quot_num, quot_int, rest_num, rest_int)
}

/*
pub fn boolean_lc<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    bool: &Boolean,
) -> LinearCombination<Scalar> {
    bool.lc(CS::one(), Scalar::one())
}
*/
