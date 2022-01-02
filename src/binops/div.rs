// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{
    cmp::Ordering,
    ops::{Div, DivAssign},
};

use fpdec_core::ten_pow;

use crate::{normalize, Decimal, DecimalError, MAX_N_FRAC_DIGITS};

#[inline(always)]
fn try_add(a: i128, b: i128) -> Result<i128, DecimalError> {
    match a.checked_add(b) {
        Some(val) => {
            return Ok(val);
        }
        None => return Err(DecimalError::InternalOverflow),
    }
}

#[inline(always)]
fn try_mul(a: i128, b: i128) -> Result<i128, DecimalError> {
    match a.checked_mul(b) {
        Some(val) => {
            return Ok(val);
        }
        None => return Err(DecimalError::InternalOverflow),
    }
}

#[inline]
pub(crate) fn div(
    divident_coeff: i128,
    divident_n_frac_digits: u8,
    divisor_coeff: i128,
    divisor_n_frac_digits: u8,
) -> Result<(i128, u8), DecimalError> {
    let (mut n_frac_digits, shift) = match divident_n_frac_digits
        .cmp(&divisor_n_frac_digits)
    {
        Ordering::Equal => (0, 0),
        Ordering::Less => (0, divisor_n_frac_digits - divident_n_frac_digits),
        _ => (divident_n_frac_digits - divisor_n_frac_digits, 0),
    };
    let mut coeff = divident_coeff / divisor_coeff;
    let mut rem = divident_coeff % divisor_coeff;
    if rem == 0 {
        if shift > 0 {
            coeff = try_mul(coeff, ten_pow(shift))?;
        } else if n_frac_digits > 0 {
            normalize(&mut coeff, &mut n_frac_digits);
        }
    } else {
        if shift > 0 {
            let ten_pow_shift = ten_pow(shift);
            coeff = try_mul(coeff, ten_pow_shift)?;
            rem = try_mul(rem, ten_pow_shift)?;
            coeff = try_add(coeff, rem / divisor_coeff)?;
            rem %= divisor_coeff;
        }
        while rem != 0 && n_frac_digits < MAX_N_FRAC_DIGITS {
            // rem < divisor
            rem = try_mul(rem, 10)?;
            // rem < 10 * divisor
            let quot = rem / divisor_coeff;
            // quot < 10
            rem %= divisor_coeff;
            n_frac_digits += 1;
            coeff = try_add(try_mul(coeff, 10)?, quot)?;
        }
        if rem != 0 {
            return Err(DecimalError::FracDigitLimitExceeded);
        }
    }
    Ok((coeff, n_frac_digits))
}

impl Div<Decimal> for Decimal {
    type Output = Decimal;

    fn div(self, rhs: Decimal) -> Self::Output {
        if rhs.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if self.eq_zero() {
            return Self::ZERO;
        }
        if rhs.eq_one() {
            return self;
        }
        match div(self.coeff, self.n_frac_digits, rhs.coeff, rhs.n_frac_digits)
        {
            Ok((coeff, n_frac_digits)) => Self::Output {
                coeff,
                n_frac_digits,
            },
            Err(error) => panic!("{}", error),
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
        assert_eq!(z.coefficient(), 25);
        assert_eq!(z.n_frac_digits(), 8);
        let x = Decimal::new_raw(17, 0);
        let y = Decimal::new_raw(-200, 2);
        let z = x / y;
        assert_eq!(z.coefficient(), -85);
        assert_eq!(z.n_frac_digits(), 1);
        let x = Decimal::new_raw(17, 8);
        let y = Decimal::new_raw(2, 0);
        let z = x / y;
        assert_eq!(z.coefficient(), 85);
        assert_eq!(z.n_frac_digits(), 9);
        let x = Decimal::new_raw(12345678901234567890, 2);
        let y = Decimal::new_raw(244140625, 6);
        let z = x / y;
        assert_eq!(z.coefficient(), 5056790077945679007744);
        assert_eq!(z.n_frac_digits(), 7);
    }

    #[test]
    fn test_div_zero() {
        let x = Decimal::new_raw(0, 9);
        let y = Decimal::new_raw(8, 0);
        let z = x / y;
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_div_by_one() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ONE;
        let z = x / y;
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 5);
        let y = Decimal::new_raw(1000000000000000, 15);
        let z = x / y;
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 5);
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
    fn test_div_frac_limit_exceeded() {
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
        assert_eq!(z.coefficient(), (&x / y).coefficient());
        assert_eq!(z.coefficient(), (x / &y).coefficient());
        assert_eq!(z.coefficient(), (&x / &y).coefficient());
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

            fn div(self, rhs: $t) -> Self::Output {
                if rhs == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self.eq_zero() {
                    return Self::ZERO;
                }
                if rhs == 1 {
                    return self;
                }
                match div(
                    self.coeff,
                    self.n_frac_digits,
                    rhs as i128,
                    0,
                ) {
                    Ok((coeff, n_frac_digits)) => Self::Output {
                        coeff,
                        n_frac_digits,
                    },
                    Err(error) => panic!("{}", error),
                }
            }
        }

        impl Div<Decimal> for $t {
            type Output = Decimal;

            fn div(self, rhs: Decimal) -> Self::Output {
                if rhs.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self == 0 {
                    return Decimal::ZERO;
                }
                if rhs.eq_one() {
                    return Self::Output {
                        coeff: self as i128,
                        n_frac_digits: 0,
                    };
                }
                match div(
                    self as i128,
                    0,
                    rhs.coeff,
                    rhs.n_frac_digits,
                ) {
                    Ok((coeff, n_frac_digits)) => Self::Output {
                        coeff,
                        n_frac_digits,
                    },
                    Err(error) => panic!("{}", error),
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
                assert_eq!(r.coefficient(), $quot);
                assert_eq!(r.n_frac_digits(), $q);
                assert_eq!(r.coefficient(), (&d / i).coefficient());
                assert_eq!(r.coefficient(), (d / &i).coefficient());
                assert_eq!(r.coefficient(), (&d / &i).coefficient());
                let z = i / d;
                assert_eq!(z, 1 / r);
                assert_eq!(z.coefficient(), (&i / d).coefficient());
                assert_eq!(z.coefficient(), (i / &d).coefficient());
                assert_eq!(z.coefficient(), (&i / &d).coefficient());
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
    fn test_div_decimal_zero_by_int() {
        let x = Decimal::new_raw(0, 3);
        let y = 123_i64;
        let z = x / y;
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_div_int_zero_by_decimal() {
        let x = 0_u32;
        let y = Decimal::new_raw(1234567, 3);
        let z = x / y;
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_div_decimal_by_int_one() {
        let x = Decimal::new_raw(17, 5);
        let y = 1_i64;
        let z = x / y;
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 5);
        let y = 1_u8;
        let z = x / y;
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 5);
    }

    #[test]
    fn test_div_int_by_decimal_one() {
        let x = 17;
        let y = Decimal::ONE;
        let z: Decimal = x / y;
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 0);
        let x = 1_u64;
        let y = Decimal::new_raw(1000, 3);
        let z = x / y;
        assert_eq!(z.coefficient(), 1);
        assert_eq!(z.n_frac_digits(), 0);
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
    fn test_div_decimal_by_int_frac_limit_exceeded() {
        let x = Decimal::new_raw(17, 2);
        let y = 3;
        let _z = x / y;
    }

    #[test]
    #[should_panic]
    fn test_div_int_by_decimal_frac_limit_exceeded() {
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
        assert_eq!(x.coefficient(), 123456789 * 2);
    }

    #[test]
    fn test_div_assign_int() {
        let mut x = Decimal::new_raw(1234567890, 9);
        x /= -10_i64;
        assert_eq!(x.coefficient(), -123456789);
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
    fn test_div_assign_decimal_by_int_frac_limit_exceeded() {
        let mut x = Decimal::new_raw(17, 9);
        let y = 3;
        x /= y;
    }

    #[test]
    #[should_panic]
    fn test_div_assign_decimal_by_decimal_frac_limit_exceeded() {
        let mut x = Decimal::new_raw(17, 9);
        let y = Decimal::new_raw(3, 4);
        x /= y;
    }
}
