// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{
    cmp::max,
    ops::{Div, DivAssign},
};

use fpdec_core::{magnitude, ten_pow};

use crate::{Decimal, DecimalError, MAX_PRECISION};

const MAGN_I128_MAX: i8 = 38;

#[inline]
fn normalize(coeff: &mut i128, exp: &mut i8) {
    if *coeff == 0 {
        *exp = 0;
    } else if *exp > 0 {
        // shift coeff
        *coeff *= ten_pow(*exp as u8);
        *exp = 0;
    } else {
        // eliminate trailing zeros in coeff
        while *coeff % 10 == 0 && *exp < 0 {
            *coeff /= 10;
            *exp += 1;
        }
    }
}

#[inline]
fn calc_fraction(
    numer: &mut i128,
    denom: &i128,
    coeff: &mut i128,
    exp: &mut i8,
) {
    // pre-condition:
    // numer < denom
    // 2 limits to be kept:
    // magnitude(coeff) <= MAGN_I128_MAX
    // exp >= -MAX_PRECISION
    let exp_min: i8 = max(
        magnitude(*coeff) as i8 - MAGN_I128_MAX + *exp,
        -(MAX_PRECISION as i8),
    );
    while *numer != 0 && *exp > exp_min {
        // numer < denom
        *numer *= 10;
        // numer < 10 * denom
        let quot = *numer / *denom;
        // quot < 10
        *numer %= *denom;
        *exp -= 1;
        *coeff = *coeff * 10 + quot;
    }
    if *numer != 0 {
        panic!("{}", DecimalError::PrecLimitExceeded);
    }
    if *exp > 0 {
        *coeff *= ten_pow(*exp as u8);
        *exp = 0;
    }
}

impl Div<Decimal> for Decimal {
    type Output = Decimal;

    fn div(self, other: Decimal) -> Self::Output {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if other.eq_one() {
            return self;
        }
        let mut exp = other.n_frac_digits as i8 - self.n_frac_digits as i8;
        let mut coeff = self.coeff / other.coeff;
        let mut rem = self.coeff % other.coeff;
        if rem == 0 {
            normalize(&mut coeff, &mut exp);
        } else {
            calc_fraction(&mut rem, &other.coeff, &mut coeff, &mut exp);
        }
        Self::Output {
            coeff,
            n_frac_digits: -exp as u8,
        }
    }
}

forward_ref_binop!(impl Div, div);

#[cfg(test)]
mod div_decimal_tests {
    use fpdec_core::mul_pow_ten;

    use super::*;

    #[test]
    fn test_div() {
        let x = Decimal::new_raw(-1000, 9);
        let y = Decimal::new_raw(-4, 0);
        let z = x / y;
        assert_eq!(z.coeff, 25);
        assert_eq!(z.n_frac_digits, 8);
        let x = Decimal::new_raw(17, 0);
        let y = Decimal::new_raw(-200, 2);
        let z = x / y;
        assert_eq!(z.coeff, -85);
        assert_eq!(z.n_frac_digits, 1);
        let x = Decimal::new_raw(17, 8);
        let y = Decimal::new_raw(2, 0);
        let z = x / y;
        assert_eq!(z.coeff, 85);
        assert_eq!(z.n_frac_digits, 9);
        let x = Decimal::new_raw(12345678901234567890, 2);
        let y = Decimal::new_raw(244140625, 6);
        let z = x / y;
        assert_eq!(z.coeff, 5056790077945679007744);
        assert_eq!(z.n_frac_digits, 7);
    }

    #[test]
    fn test_div_zero() {
        let x = Decimal::new_raw(0, 9);
        let y = Decimal::new_raw(8, 0);
        let z = x / y;
        assert_eq!(z.coeff, 0);
        assert_eq!(z.n_frac_digits, 0);
    }

    #[test]
    fn test_div_by_one() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ONE;
        let z = x / y;
        assert_eq!(z.coeff, 17);
        assert_eq!(z.n_frac_digits, 5);
        let y = Decimal::new_raw(1000000000000000, 15);
        let z = x / y;
        assert_eq!(z.coeff, 17);
        assert_eq!(z.n_frac_digits, 5);
    }

    #[test]
    #[should_panic]
    fn test_div_by_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::new_raw(0, 7);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_prec_limit_exceeded() {
        let x = Decimal::new_raw(3, 0);
        let y = Decimal::new_raw(17, 9);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_overflow() {
        let x = Decimal::new_raw(mul_pow_ten(17, 20), 0);
        let y = Decimal::new_raw(2, 19);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_internal_overflow() {
        let x = Decimal::new_raw(i128::MAX - 1, 0);
        let y = Decimal::new_raw(i128::MAX, 0);
        let _z = x / y;
    }

    #[test]
    fn test_div_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x / y;
        assert_eq!(z.coeff, (&x / y).coeff);
        assert_eq!(z.coeff, (x / &y).coeff);
        assert_eq!(z.coeff, (&x / &y).coeff);
    }
}

macro_rules! impl_div_decimal_and_int {
    () => {
        impl_div_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl Div<$t> for Decimal {
            type Output = Decimal;

            fn div(self, other: $t) -> Self::Output {
                if other == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if other == 1 {
                    return self;
                }
                let mut exp = -(self.n_frac_digits as i8);
                let mut coeff = self.coeff / other as i128;
                let mut rem = self.coeff % other as i128;
                if rem == 0 {
                    normalize(&mut coeff, &mut exp);
                } else {
                    calc_fraction(&mut rem, &(other as i128), &mut coeff, &mut exp);
                }
                Self::Output {
                    coeff,
                    n_frac_digits: -exp as u8,
                }
            }
        }

        impl Div<Decimal> for $t {
            type Output = Decimal;

            fn div(self, other: Decimal) -> Self::Output {
                if other.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if other.eq_one() {
                    return Self::Output {
                        coeff: self as i128,
                        n_frac_digits: 0,
                    };
                }
                let mut exp = other.n_frac_digits as i8;
                let mut coeff = self as i128 / other.coeff;
                let mut rem = self as i128 % other.coeff;
                if rem == 0 {
                    normalize(&mut coeff, &mut exp);
                } else {
                    calc_fraction(&mut rem, &other.coeff, &mut coeff, &mut exp);
                }
                Self::Output {
                    coeff,
                    n_frac_digits: -exp as u8,
                }
            }
        }
        )*
    }
}

impl_div_decimal_and_int!();
forward_ref_binop_decimal_int!(impl Div, div);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_integer_tests {
    use fpdec_core::mul_pow_ten;

    use super::*;

    macro_rules! gen_div_integer_tests {
        ($func:ident, $t:ty, $den:expr, $p:expr, $num:expr, $q:expr,
         $quot:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($num, $p);
                let i: $t = $den;
                let r = d / i;
                assert_eq!(r.coeff, $quot);
                assert_eq!(r.precision(), $q);
                assert_eq!(r.coeff, (&d / i).coeff);
                assert_eq!(r.coeff, (d / &i).coeff);
                assert_eq!(r.coeff, (&d / &i).coeff);
                let z = i / d;
                assert_eq!(z, 1 / r);
                assert_eq!(z.coeff, (&i / d).coeff);
                assert_eq!(z.coeff, (i / &d).coeff);
                assert_eq!(z.coeff, (&i / &d).coeff);
            }
        };
    }

    gen_div_integer_tests!(test_div_u8, u8, 25, 2, -1, 4, -4);
    gen_div_integer_tests!(test_div_i8, i8, 125, 0, 250, 0, 2);
    gen_div_integer_tests!(test_div_u16, u16, 1600, 4, 80, 6, 5);
    gen_div_integer_tests!(test_div_i16, i16, -5, 4, 390625, 4, -78125);
    gen_div_integer_tests!(test_div_u32, u32, 78125, 3, 20, 9, 256);
    gen_div_integer_tests!(test_div_i32, i32, -4, 9, -1000, 8, 25);
    gen_div_integer_tests!(
        test_div_u64,
        u64,
        137438953472,
        1,
        1,
        38,
        72759576141834259033203125
    );
    gen_div_integer_tests!(test_div_i64, i64, 244140625, 2, -488281250, 2, -2);
    gen_div_integer_tests!(test_div_i128, i128, 5005, 4, 2002, 5, 4);

    #[test]
    fn test_div_decimal_by_int_one() {
        let x = Decimal::new_raw(17, 5);
        let y = 1_i64;
        let z = x / y;
        assert_eq!(z.coeff, 17);
        assert_eq!(z.n_frac_digits, 5);
        let y = 1_u8;
        let z = x / y;
        assert_eq!(z.coeff, 17);
        assert_eq!(z.n_frac_digits, 5);
    }

    #[test]
    fn test_div_int_by_decimal_one() {
        let x = 17;
        let y = Decimal::ONE;
        let z: Decimal = x / y;
        assert_eq!(z.coeff, 17);
        assert_eq!(z.n_frac_digits, 0);
        let x = 1_u64;
        let y = Decimal::new_raw(1000, 3);
        let z = x / y;
        assert_eq!(z.coeff, 1);
        assert_eq!(z.n_frac_digits, 0);
    }

    #[test]
    #[should_panic]
    fn test_div_decimal_by_int_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = 0_i32;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_zero() {
        let x = 25;
        let y = Decimal::new_raw(0, 5);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_decimal_by_int_prec_limit_exceeded() {
        let x = Decimal::new_raw(17, 2);
        let y = 3;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_prec_limit_exceeded() {
        let x = 3;
        let y = Decimal::new_raw(17, 2);
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_overflow() {
        let x = mul_pow_ten(17, 20);
        let y = Decimal::new_raw(2, 19);
        let _z = x / y;
    }
}

forward_op_assign!(impl DivAssign, div_assign, Div, div);

#[cfg(test)]
mod div_assign_tests {
    use super::*;

    #[test]
    fn test_div_assign_decimal() {
        let mut x = Decimal::new_raw(1234567890, 9);
        x /= Decimal::new_raw(5000, 3);
        assert_eq!(x.coeff, 123456789 * 2);
    }

    #[test]
    fn test_div_assign_int() {
        let mut x = Decimal::new_raw(1234567890, 9);
        x /= -10_i64;
        assert_eq!(x.coeff, -123456789);
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_int_zero() {
        let mut x = Decimal::new_raw(17, 9);
        let y = 0_i32;
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_decimal_zero() {
        let mut x = Decimal::new_raw(25, 9);
        let y = Decimal::ZERO;
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_int_prec_limit_exceeded() {
        let mut x = Decimal::new_raw(17, 9);
        let y = 3;
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_decimal_prec_limit_exceeded() {
        let mut x = Decimal::new_raw(17, 9);
        let y = Decimal::new_raw(3, 4);
        x /= y;
    }
}
