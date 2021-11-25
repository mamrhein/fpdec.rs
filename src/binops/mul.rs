// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::{Mul, MulAssign};

use crate::Decimal;

impl Mul<Decimal> for Decimal {
    type Output = Self;

    #[inline(always)]
    fn mul(self, other: Decimal) -> Self::Output {
        // TODO: handle self.n_frac_digits + other.n_frac_digits > MAX_N_FRAC_DIGITS
        Self::Output {
            coeff: self.coeff * other.coeff,
            n_frac_digits: self.n_frac_digits + other.n_frac_digits,
        }
    }
}

forward_ref_binop!(impl Mul, mul);

#[cfg(test)]
mod mul_decimal_tests {
    use super::*;

    #[test]
    fn test_mul_same_n_frac_digits() {
        let x = Decimal::new_raw(1234567890, 4);
        let y = x * x;
        assert_eq!(y.n_frac_digits(), 2 * x.n_frac_digits());
        assert_eq!(y.coeff, x.coeff * x.coeff);
    }

    #[test]
    fn test_mul_different_n_frac_digits() {
        let x = Decimal::new_raw(1234567890, 5);
        let y = Decimal::new_raw(890, 1);
        let z = x * y;
        assert_eq!(z.n_frac_digits(), 6);
        assert_eq!(z.coeff, x.coeff * y.coeff);
        let z = y * x;
        assert_eq!(z.n_frac_digits(), 6);
        assert_eq!(z.coeff, x.coeff * y.coeff);
        let z = x * Decimal::NEG_ONE;
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
        assert_eq!(z.coeff, -x.coeff);
    }

    #[test]
    #[should_panic]
    fn test_mul_pos_overflow() {
        let x = Decimal::new_raw(i128::MAX / 2 + 1, 4);
        let _y = x * Decimal::TWO;
    }

    #[test]
    #[should_panic]
    fn test_mul_neg_one_overflow() {
        let x = Decimal::new_raw(i128::MIN, 3);
        let _y = x * Decimal::NEG_ONE;
    }

    #[test]
    #[should_panic]
    fn test_mul_neg_overflow() {
        let x = Decimal::new_raw(i128::MIN / 2 - 1, 3);
        let _y = x * Decimal::TWO;
    }

    #[test]
    fn test_mul_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x * y;
        assert_eq!(z.coeff, (&x * y).coeff);
        assert_eq!(z.coeff, (x * &y).coeff);
        assert_eq!(z.coeff, (&x * &y).coeff);
    }
}

macro_rules! impl_mul_decimal_and_int {
    () => {
        impl_mul_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl Mul<$t> for Decimal {
            type Output = Decimal;

            #[inline(always)]
            fn mul(self, other: $t) -> Self::Output {
                Self::Output{
                    coeff: self.coeff * other as i128,
                    n_frac_digits: self.n_frac_digits,
                }
            }
        }

        impl Mul<Decimal> for $t {
            type Output = Decimal;

            #[inline(always)]
            fn mul(self, other: Decimal) -> Self::Output {
                Self::Output{
                    coeff: self as i128 * other.coeff,
                    n_frac_digits: other.n_frac_digits,
                }
            }
        }
        )*
    }
}

impl_mul_decimal_and_int!();
forward_ref_binop_decimal_int!(impl Mul, mul);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod mul_integer_tests {
    use super::*;

    macro_rules! gen_mul_integer_tests {
        ($func:ident, $t:ty, $n_frac_digits:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $n_frac_digits);
                let i = <$t>::MAX;
                let r = d * i;
                assert_eq!(r.n_frac_digits(), d.n_frac_digits());
                assert_eq!(r.coeff, i as i128 * $coeff);
                assert_eq!(r.coeff, (&d * i).coeff);
                assert_eq!(r.coeff, (d * &i).coeff);
                assert_eq!(r.coeff, (&d * &i).coeff);
                let z = i * d;
                assert_eq!(z.n_frac_digits(), r.n_frac_digits());
                assert_eq!(z.coeff, r.coeff);
                assert_eq!(z.coeff, (&i * d).coeff);
                assert_eq!(z.coeff, (i * &d).coeff);
                assert_eq!(z.coeff, (&i * &d).coeff);
            }
        };
    }

    gen_mul_integer_tests!(test_mul_u8, u8, 2, -1);
    gen_mul_integer_tests!(test_mul_i8, i8, 0, 123);
    gen_mul_integer_tests!(test_mul_u16, u16, 4, 11);
    gen_mul_integer_tests!(test_mul_i16, i16, 4, 1234567);
    gen_mul_integer_tests!(test_mul_u32, u32, 1, 0);
    gen_mul_integer_tests!(test_mul_i32, i32, 9, -1234);
    gen_mul_integer_tests!(test_mul_u64, u64, 3, 321);
    gen_mul_integer_tests!(test_mul_i64, i64, 7, -12345678901234567890);

    #[test]
    fn test_mul_i128() {
        let coeff = 748_i128;
        let d = Decimal::new_raw(coeff, 2);
        let i = 12345_i128;
        let r = d * i;
        assert_eq!(r.n_frac_digits(), d.n_frac_digits());
        assert_eq!(r.coeff, i * coeff);
        assert_eq!(r.coeff, (&d * i).coeff);
        assert_eq!(r.coeff, (d * &i).coeff);
        assert_eq!(r.coeff, (&d * &i).coeff);
        let z = i * d;
        assert_eq!(z.n_frac_digits(), r.n_frac_digits());
        assert_eq!(z.coeff, r.coeff);
        assert_eq!(z.coeff, (&i * d).coeff);
        assert_eq!(z.coeff, (i * &d).coeff);
        assert_eq!(z.coeff, (&i * &d).coeff);
    }
}

forward_op_assign!(impl MulAssign, mul_assign, Mul, mul);

#[cfg(test)]
mod mul_assign_tests {
    use super::*;

    #[test]
    fn test_mul_assign_decimal() {
        let mut x = Decimal::new_raw(123456, 2);
        let y = Decimal::TWO;
        x *= y;
        assert_eq!(x.coeff, 123456_i128 * 2);
        let z = &y;
        x *= z;
        assert_eq!(x.coeff, 123456_i128 * 4);
    }

    #[test]
    fn test_mul_assign_int() {
        let mut x = Decimal::new_raw(123456, 2);
        x *= 2_i8;
        assert_eq!(x.coeff, 123456_i128 * 2);
        x *= &-1234567890_i128;
        assert_eq!(x.coeff, 123456_i128 * 2 * -1234567890_i128);
    }

    #[test]
    #[should_panic]
    fn test_mul_assign_pos_overflow() {
        let mut x = Decimal::new_raw(i128::MAX / 2 + 1, 4);
        x *= 2;
    }

    #[test]
    #[should_panic]
    fn test_mul_assign_neg_overflow() {
        let mut x = Decimal::new_raw(i128::MIN / 5 - 1, 1);
        x *= 5;
    }
}
