// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::ops::{Div, DivAssign};

use crate::{
    binops::div_rounded::checked_div_rounded, normalize, Decimal, DecimalError,
    MAX_N_FRAC_DIGITS,
};

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
        let mut n_frac_digits = MAX_N_FRAC_DIGITS;
        if let Some(mut coeff) = checked_div_rounded(
            self.coeff,
            self.n_frac_digits,
            rhs.coeff,
            rhs.n_frac_digits,
            n_frac_digits,
        ) {
            normalize(&mut coeff, &mut n_frac_digits);
            Self::Output {
                coeff,
                n_frac_digits,
            }
        } else {
            panic!("{}", DecimalError::InternalOverflow);
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
    fn test_div_frac_limit_exceeded() {
        let x = Decimal::new_raw(3, 0);
        let y = Decimal::new_raw(17, 9);
        let z = x / y;
        assert_eq!(z.coefficient(), 176470588235294117647058824);
        assert_eq!(z.n_frac_digits(), 18);
        let z = Decimal::new_raw(1, 0) / x;
        assert_eq!(z.coefficient(), 333333333333333333);
        assert_eq!(z.n_frac_digits(), 18);
    }

    #[test]
    fn test_div_zero() {
        let x = Decimal::new_raw(0, 9);
        let y = Decimal::new_raw(8, 0);
        let z = x / y;
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    // corner case where divident * shift exceeds i128::MAX, but result doesn't
    #[test]
    fn test_div_internal_overflow() {
        let x = Decimal::new_raw(i128::MAX - 1, 0);
        let y = Decimal::new_raw(i128::MAX, 0);
        let z = x / y;
        assert_eq!(z.coefficient(), 1);
        assert_eq!(z.n_frac_digits(), 0);
        let z = y / x;
        assert_eq!(z.coefficient(), 1);
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
    fn test_div_overflow() {
        let x = Decimal::new_raw(mul_pow_ten(17, 20), 0);
        let y = Decimal::new_raw(2, 19);
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
                let mut n_frac_digits = MAX_N_FRAC_DIGITS;
                if let Some(mut coeff) = checked_div_rounded(
                    self.coeff,
                    self.n_frac_digits,
                    rhs as i128,
                    0,
                    n_frac_digits,
                ) {
                    normalize(&mut coeff, &mut n_frac_digits);
                    Self::Output {
                        coeff,
                        n_frac_digits,
                    }
                } else {
                    panic!("{}", DecimalError::InternalOverflow);
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
                let mut n_frac_digits = MAX_N_FRAC_DIGITS;
                if let Some(mut coeff) = checked_div_rounded(
                    self as i128,
                    0,
                    rhs.coeff,
                    rhs.n_frac_digits,
                    n_frac_digits,
                ) {
                    normalize(&mut coeff, &mut n_frac_digits);
                    Self::Output {
                        coeff,
                        n_frac_digits,
                    }
                } else {
                    panic!("{}", DecimalError::InternalOverflow);
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
    gen_div_integer_tests!(test_div_u64, u64, 16384000, 0, 1, 17, 6103515625);
    gen_div_integer_tests!(test_div_i64, i64, 244140625, 2, -488281250, 2, -2);
    gen_div_integer_tests!(test_div_i128, i128, 5005, 4, 2002, 5, 4);

    #[test]
    fn test_div_decimal_by_int_frac_limit_exceeded() {
        let x = Decimal::new_raw(17, 2);
        let y = 3_i32;
        let z = x / y;
        assert_eq!(z.coefficient(), 56666666666666667);
        assert_eq!(z.n_frac_digits(), 18);
    }

    #[test]
    fn test_div_int_by_decimal_frac_limit_exceeded() {
        let x = 3_i32;
        let y = Decimal::new_raw(17, 2);
        let z = x / y;
        assert_eq!(z.coefficient(), 17647058823529411765);
        assert_eq!(z.n_frac_digits(), 18);
    }

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
        assert_eq!(x.n_frac_digits(), 9);
    }

    #[test]
    fn test_div_assign_int() {
        let mut x = Decimal::new_raw(1234567890, 9);
        x /= -10_i64;
        assert_eq!(x.coefficient(), -123456789);
        assert_eq!(x.n_frac_digits(), 9);
    }

    #[test]
    fn test_div_assign_decimal_by_int_frac_limit_exceeded() {
        let mut x = Decimal::new_raw(17, 9);
        let y = 3_i16;
        x /= y;
        assert_eq!(x.coefficient(), 5666666667);
        assert_eq!(x.n_frac_digits(), 18);
    }

    #[test]
    fn test_div_assign_decimal_by_decimal_frac_limit_exceeded() {
        let mut x = Decimal::new_raw(3, 4);
        let y = Decimal::new_raw(17, 9);
        x /= y;
        assert_eq!(x.coefficient(), 17647058823529411764706);
        assert_eq!(x.n_frac_digits(), 18);
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
}
