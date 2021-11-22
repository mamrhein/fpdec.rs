// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::cmp::{min, Ordering};

use fpdec_core::{checked_mul_pow_ten, magnitude, ten_pow};

use crate::{rounding::div_i128_rounded, Decimal, DecimalError};

const MAGN_I128_MAX: u8 = 38;

/// Division giving a result rounded to fit a given number of fractional
/// digits.
pub trait DivRounded<Rhs = Self> {
    /// The resulting type after applying `div_rounded`.
    type Output;

    /// Returns `self` / `other`, rounded to `n_frac_digits`.
    fn div_rounded(self, rhs: Rhs, n_frac_digits: u8) -> Self::Output;
}

#[inline]
fn div_rounded(
    divident: i128,
    divident_prec: u8,
    divisor: i128,
    divisor_prec: u8,
    n_frac_digits: u8,
) -> i128 {
    let mut shift = n_frac_digits + divisor_prec;
    match divident_prec.cmp(&shift) {
        Ordering::Equal => div_i128_rounded(divident, divisor, None),
        Ordering::Less => {
            // divident needs to be shifted
            shift -= divident_prec;
            if let Some(shifted_divident) = checked_mul_pow_ten(divident, shift)
            {
                div_i128_rounded(shifted_divident, divisor, None)
            } else {
                let magn_divident = magnitude(divident);
                let magn_shifted_divident = magn_divident + shift;
                if (magn_shifted_divident - magnitude(divisor)) > MAGN_I128_MAX
                {
                    panic!("{}", DecimalError::InternalOverflow);
                }
                let mut coeff = divident / divisor;
                let mut rem = divident % divisor;
                let mut rem_shift = shift;
                let mut step_shift =
                    min(rem_shift, MAGN_I128_MAX - magnitude(rem));
                while step_shift < rem_shift {
                    coeff *= ten_pow(step_shift);
                    rem *= ten_pow(step_shift);
                    coeff += rem / divisor;
                    rem %= divisor;
                    rem_shift -= step_shift;
                    step_shift = min(rem_shift, MAGN_I128_MAX - magnitude(rem));
                }
                coeff *= ten_pow(step_shift);
                rem *= ten_pow(step_shift);
                coeff += div_rounded(
                    rem,
                    divident_prec,
                    divisor,
                    divident_prec,
                    n_frac_digits,
                );
                coeff
            }
        }
        Ordering::Greater => {
            // divisor needs to be shifted
            // divident_prec > shift
            shift = divident_prec - shift;
            // shift < divident_prec => shift < 38 => ten_pow(shift) is safe
            // if let Some(shifted_divisor) = checked_mul_pow_ten(divisor,
            // shift) {     div_i128_rounded(divident,
            // shifted_divisor, None) }
            div_i128_rounded(divident / divisor, ten_pow(shift), None)
        }
    }
}

impl DivRounded<Decimal> for Decimal {
    type Output = Self;

    fn div_rounded(self, other: Decimal, n_frac_digits: u8) -> Self::Output {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if self.eq_zero() {
            return Self::ZERO;
        }
        let coeff = div_rounded(
            self.coeff,
            self.n_frac_digits,
            other.coeff,
            other.n_frac_digits,
            n_frac_digits,
        );
        Self::Output {
            coeff,
            n_frac_digits,
        }
    }
}

forward_ref_binop_rounded!(impl DivRounded, div_rounded);

#[cfg(test)]
mod div_rounded_decimal_tests {
    use fpdec_core::mul_pow_ten;

    use super::*;

    #[test]
    fn test_div_rounded() {
        let x = Decimal::new_raw(17, 0);
        let y = Decimal::new_raw(-201, 2);
        let z = x.div_rounded(y, 2);
        assert_eq!(z.coeff, -846);
        assert_eq!(z.n_frac_digits, 2);
        let x = Decimal::new_raw(17, 8);
        let y = Decimal::new_raw(204, 3);
        let z = x.div_rounded(y, 8);
        assert_eq!(z.coeff, 83);
        assert_eq!(z.n_frac_digits, 8);
        let x = Decimal::new_raw(12345678901234567890, 2);
        let y = Decimal::new_raw(244140625, 6);
        let z = x.div_rounded(y, 9);
        assert_eq!(z.coeff, 505679007794567900774400);
        assert_eq!(z.n_frac_digits, 9);
    }

    #[test]
    fn test_div_rounded_by_one() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ONE;
        let z = x.div_rounded(y, 4);
        assert_eq!(z.coeff, 2);
        assert_eq!(z.n_frac_digits, 4);
        let y = Decimal::new_raw(1000000000, 9);
        let z = x.div_rounded(y, 6);
        assert_eq!(z.coeff, 170);
        assert_eq!(z.n_frac_digits, 6);
    }

    // corner case: shifting divident overflows, stepwise algorithm must be used
    #[test]
    fn test_div_rounded_stepwise() {
        let x = Decimal::new_raw(13, 1);
        let y = Decimal::new_raw(20, 29);
        let z = x.div_rounded(y, 10);
        assert_eq!(z.coeff, 65000000000000000000000000000000000000);
        assert_eq!(z.n_frac_digits, 10);
    }

    #[test]
    fn test_div_zero_rounded() {
        let x = Decimal::new_raw(0, 5);
        let y = Decimal::new_raw(17, 1);
        let z = x.div_rounded(y, 3);
        assert_eq!(z.coeff, 0);
        assert_eq!(z.n_frac_digits, 0);
        let z = x.div_rounded(y, 29);
        assert_eq!(z.coeff, 0);
        assert_eq!(z.n_frac_digits, 0);
    }

    #[test]
    #[should_panic]
    fn test_div_rounded_by_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ZERO;
        let _z = x.div_rounded(y, 5);
    }

    #[test]
    #[should_panic]
    fn test_div_rounded_overflow() {
        let x = Decimal::new_raw(mul_pow_ten(17, 20), 0);
        let y = Decimal::new_raw(2, 19);
        let _z = x.div_rounded(y, 0);
    }

    #[test]
    fn test_div_rounded_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 4);
        let z = x.div_rounded(y, 2);
        let a = DivRounded::div_rounded(&x, y, 2);
        assert_eq!(a.coeff, z.coeff);
        let a = DivRounded::div_rounded(x, &y, 2);
        assert_eq!(a.coeff, z.coeff);
        let a = DivRounded::div_rounded(&x, &y, 2);
        assert_eq!(a.coeff, z.coeff);
    }
}

macro_rules! impl_div_rounded_decimal_and_int {
    () => {
        impl_div_rounded_decimal_and_int!(
            u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    ($($t:ty),*) => {
        $(
        impl DivRounded<$t> for Decimal {
            type Output = Self;

            fn div_rounded(self, other: $t, n_frac_digits: u8) -> Self::Output {
                if other == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self.eq_zero() {
                    return Self::ZERO;
                }
                let coeff = div_rounded(
                    self.coeff,
                    self.n_frac_digits,
                    other as i128,
                    0_u8,
                    n_frac_digits,
                );
                Self::Output {
                    coeff,
                    n_frac_digits,
                }
            }
        }

        impl<'a> DivRounded<$t> for &'a Decimal
        where
            Decimal: DivRounded<$t>,
        {
            type Output = <Decimal as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, other: $t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, other, n_frac_digits)
            }
        }

        impl DivRounded<&$t> for Decimal
        where
            Decimal: DivRounded<$t>,
        {
            type Output = <Decimal as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, other: &$t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(self, *other, n_frac_digits)
            }
        }

        impl DivRounded<&$t> for &Decimal
        where
            Decimal: DivRounded<$t>,
        {
            type Output = <Decimal as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, other: &$t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, *other, n_frac_digits)
            }
        }

        impl DivRounded<Decimal> for $t {
            type Output = Decimal;

            fn div_rounded(self, other: Decimal, n_frac_digits: u8) -> Self::Output {
                if other.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self == 0 {
                    return Decimal::ZERO;
                }
                let coeff = div_rounded(
                    self as i128,
                    0_u8,
                    other.coeff,
                    other.n_frac_digits,
                    n_frac_digits,
                );
                Self::Output {
                    coeff,
                    n_frac_digits,
                }
            }
        }

        impl<'a> DivRounded<Decimal> for &'a $t
        where
            $t: DivRounded<Decimal>,
        {
            type Output = <$t as DivRounded<Decimal>>::Output;

            #[inline(always)]
            fn div_rounded(self, other: Decimal, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, other, n_frac_digits)
            }
        }

        impl DivRounded<&Decimal> for $t
        where
            $t: DivRounded<Decimal>,
        {
            type Output = <$t as DivRounded<Decimal>>::Output;

            #[inline(always)]
            fn div_rounded(self, other: &Decimal, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(self, *other, n_frac_digits)
            }
        }

        impl DivRounded<&Decimal> for &$t
        where
            $t: DivRounded<Decimal>,
        {
            type Output = <$t as DivRounded<Decimal>>::Output;

            #[inline(always)]
            fn div_rounded(self, other: &Decimal, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, *other, n_frac_digits)
            }
        }
        )*
    }
}

impl_div_rounded_decimal_and_int!();

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_rounded_decimal_by_int_tests {
    use super::*;

    macro_rules! gen_div_rounded_decimal_by_int_tests {
        ($func:ident, $p:expr, $coeff:expr, $i:expr, $r:expr,
         $res_coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i = $i;
                let r = d.div_rounded(i, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
                let r = (&d).div_rounded(i, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
                let r = d.div_rounded(&i, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
                let r = (&d).div_rounded(&i, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
            }
        };
    }

    gen_div_rounded_decimal_by_int_tests!(test_u8, 2, -1, 3_u8, 5, -333);
    gen_div_rounded_decimal_by_int_tests!(test_i8, 0, -12, -3_i8, 5, 400000);
    gen_div_rounded_decimal_by_int_tests!(test_u16, 2, -1, 3_u16, 5, -333);
    gen_div_rounded_decimal_by_int_tests!(test_i16, 3, -12, -3_i16, 5, 400);
    gen_div_rounded_decimal_by_int_tests!(
        test_u32,
        4,
        u32::MAX as i128,
        1_u32,
        5,
        u32::MAX as i128 * 10_i128
    );
    gen_div_rounded_decimal_by_int_tests!(
        test_i32, 3, 12345, -328_i32, 5, -3764
    );
    gen_div_rounded_decimal_by_int_tests!(test_u64, 9, -1, 2_u64, 5, 0);
    gen_div_rounded_decimal_by_int_tests!(
        test_i64,
        3,
        u64::MAX as i128,
        i64::MIN,
        2,
        0
    );
    gen_div_rounded_decimal_by_int_tests!(
        test_i128,
        0,
        12345678901234567890,
        987654321_i128,
        5,
        1249999988734375
    );
}

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_rounded_int_by_decimal_tests {
    use super::*;

    macro_rules! gen_div_rounded_int_by_decimal_tests {
        ($func:ident, $p:expr, $coeff:expr, $i:expr, $r:expr,
         $res_coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i = $i;
                let r = i.div_rounded(d, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
                let r = (&i).div_rounded(d, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
                let r = i.div_rounded(&d, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
                let r = (&i).div_rounded(&d, $r);
                assert_eq!(r.coeff, $res_coeff);
                assert_eq!(r.n_frac_digits, $r);
            }
        };
    }

    gen_div_rounded_int_by_decimal_tests!(test_u8, 2, -14, 3_u8, 5, -2142857);
    gen_div_rounded_int_by_decimal_tests!(test_i8, 0, -12, -3_i8, 5, 25000);
    gen_div_rounded_int_by_decimal_tests!(test_u16, 2, -17, 3_u16, 5, -1764706);
    gen_div_rounded_int_by_decimal_tests!(test_i16, 3, -12, -3_i16, 2, 25000);
    gen_div_rounded_int_by_decimal_tests!(
        test_u32,
        4,
        u32::MAX as i128,
        1_u32,
        9,
        2328
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_i32, 3, 12345, -328_i32, 5, -2656946
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_u64,
        9,
        -1,
        2_u64,
        5,
        -200000000000000
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_i64,
        3,
        u64::MAX as i128,
        i64::MIN,
        2,
        -50000
    );
    gen_div_rounded_int_by_decimal_tests!(
        test_i128,
        0,
        1234567890,
        987654321987654321_i128,
        1,
        8000000081
    );
}
