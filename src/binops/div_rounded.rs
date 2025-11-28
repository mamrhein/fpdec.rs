// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::cmp::Ordering;

use fpdec_core::{
    checked_mul_pow_ten, i128_div_rounded, i128_shifted_div_rounded, ten_pow,
    MAX_N_FRAC_DIGITS,
};

use crate::{Decimal, DecimalError};

// const MAGN_I128_MAX: u8 = 38;

/// Division giving a result rounded to fit a given number of fractional
/// digits.
pub trait DivRounded<Rhs = Self> {
    /// The resulting type after applying `div_rounded`.
    type Output;

    /// Returns `self` / `rhs`, rounded to `n_frac_digits`, according to the
    /// current [RoundingMode](crate::RoundingMode).
    ///
    /// # Panics
    ///
    /// Panics if `rhs` equals zero or the resulting value can not be
    /// represented by `Self::Output`!
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, DivRounded};
    /// let divident = -322_i32;
    /// let divisor = 3_i32;
    /// let res = divident.div_rounded(divisor, 0);
    /// assert_eq!(res.to_string(), "-107");
    /// let d = Dec!(28.27093);
    /// let q = 5_u32;
    /// let r = d.div_rounded(q, 4);
    /// assert_eq!(r.to_string(), "5.6542");
    /// let q = Dec!(0.03);
    /// let r = d.div_rounded(q, 3);
    /// assert_eq!(r.to_string(), "942.364");
    /// ```
    fn div_rounded(self, rhs: Rhs, n_frac_digits: u8) -> Self::Output;
}

#[allow(clippy::integer_division)]
pub(crate) fn checked_div_rounded(
    divident_coeff: i128,
    divident_n_frac_digits: u8,
    divisor_coeff: i128,
    divisor_n_frac_digits: u8,
    n_frac_digits: u8,
) -> Option<i128> {
    let mut shift = n_frac_digits + divisor_n_frac_digits;
    match divident_n_frac_digits.cmp(&shift) {
        Ordering::Equal => {
            Some(i128_div_rounded(divident_coeff, divisor_coeff, None))
        }
        Ordering::Less => {
            // divident coeff needs to be shifted
            shift -= divident_n_frac_digits;
            // 0 < shift <= 36
            if let Some(shifted_divident) =
                checked_mul_pow_ten(divident_coeff, shift)
            {
                Some(i128_div_rounded(shifted_divident, divisor_coeff, None))
            } else {
                i128_shifted_div_rounded(
                    divident_coeff,
                    shift,
                    divisor_coeff,
                    None,
                )
            }
        }
        Ordering::Greater => {
            // divisor coeff needs to be shifted, but instead of calculating
            // divident / (divisor * 10 ^ shift)
            // we can calculate
            // (divident / divisor) / 10 ^ shift
            // thus avoiding i128 overflow.
            // divident_n_frac_digits > shift
            shift = divident_n_frac_digits - shift;
            // shift < divident_n_frac_digits => shift < 18 => ten_pow(shift)
            // is safe
            Some(i128_div_rounded(
                divident_coeff / divisor_coeff,
                ten_pow(shift),
                None,
            ))
        }
    }
}

impl DivRounded<Self> for Decimal {
    type Output = Self;

    fn div_rounded(self, rhs: Self, n_frac_digits: u8) -> Self::Output {
        #[allow(clippy::manual_assert)]
        if n_frac_digits > MAX_N_FRAC_DIGITS {
            panic!("{}", DecimalError::MaxNFracDigitsExceeded);
        }
        #[allow(clippy::manual_assert)]
        if rhs.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if self.eq_zero() {
            return Self::ZERO;
        }
        if let Some(coeff) = checked_div_rounded(
            self.coeff,
            self.n_frac_digits,
            rhs.coeff,
            rhs.n_frac_digits,
            n_frac_digits,
        ) {
            Self::Output {
                coeff,
                n_frac_digits,
            }
        } else {
            panic!("{}", DecimalError::InternalOverflow);
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
        assert_eq!(z.coefficient(), -846);
        assert_eq!(z.n_frac_digits(), 2);
        let x = Decimal::new_raw(17654321, 8);
        let y = Decimal::new_raw(204, 3);
        let z = x.div_rounded(y, 2);
        assert_eq!(z.coefficient(), 87);
        assert_eq!(z.n_frac_digits(), 2);
        let x = Decimal::new_raw(12345678901234567890, 2);
        let y = Decimal::new_raw(244140625, 6);
        let z = x.div_rounded(y, 9);
        assert_eq!(z.coefficient(), 505679007794567900774400);
        assert_eq!(z.n_frac_digits(), 9);
        let x = Decimal::new_raw(1234567, 5);
        let y = Decimal::new_raw(625, 2);
        let z = x.div_rounded(y, 3);
        assert_eq!(z.coefficient(), 1975);
        assert_eq!(z.n_frac_digits(), 3);
    }

    #[test]
    fn test_div_rounded_to_int() {
        let x = Decimal::new_raw(17, 0);
        let y = Decimal::new_raw(200, 2);
        let z = x.div_rounded(y, 0);
        assert_eq!(z.coefficient(), 8);
        assert_eq!(z.n_frac_digits(), 0);
        let y = Decimal::new_raw(3, 0);
        let z = x.div_rounded(y, 0);
        assert_eq!(z.coefficient(), 6);
        let x = Decimal::new_raw(170000, 4);
        let y = Decimal::new_raw(3, 0);
        let z = x.div_rounded(y, 0);
        assert_eq!(z.coefficient(), 6);
    }

    #[test]
    fn test_div_zero_rounded() {
        let x = Decimal::new_raw(0, 5);
        let y = Decimal::new_raw(17, 1);
        let z = x.div_rounded(y, 3);
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
        let z = x.div_rounded(y, 18);
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_div_rounded_by_one() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ONE;
        let z = x.div_rounded(y, 4);
        assert_eq!(z.coefficient(), 2);
        assert_eq!(z.n_frac_digits(), 4);
        let y = Decimal::new_raw(1000000000, 9);
        let z = x.div_rounded(y, 6);
        assert_eq!(z.coefficient(), 170);
        assert_eq!(z.n_frac_digits(), 6);
    }

    // corner case: shifting divident overflows, stepwise algorithm must be
    // used
    #[test]
    fn test_div_rounded_stepwise() {
        let x = Decimal::new_raw(mul_pow_ten(13, 11), 1);
        let y = Decimal::new_raw(20, 18);
        let z = x.div_rounded(y, 10);
        assert_eq!(z.coefficient(), 65000000000000000000000000000000000000);
        assert_eq!(z.n_frac_digits(), 10);
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
        assert_eq!(a.coefficient(), z.coefficient());
        let a = DivRounded::div_rounded(x, &y, 2);
        assert_eq!(a.coefficient(), z.coefficient());
        let a = DivRounded::div_rounded(&x, &y, 2);
        assert_eq!(a.coefficient(), z.coefficient());
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

            fn div_rounded(self, rhs: $t, n_frac_digits: u8) -> Self::Output {
                if rhs == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self.eq_zero() {
                    return Self::ZERO;
                }
                if let Some(coeff) = checked_div_rounded(
                    self.coeff,
                    self.n_frac_digits,
                    i128::from(rhs),
                    0_u8,
                    n_frac_digits,
                ) {
                    Self::Output {
                        coeff,
                        n_frac_digits,
                    }
                } else {
                    panic!("{}", DecimalError::InternalOverflow);
                }
            }
        }

        impl<'a> DivRounded<$t> for &'a Decimal
        where
            Decimal: DivRounded<$t>,
        {
            type Output = <Decimal as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: $t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, rhs, n_frac_digits)
            }
        }

        impl DivRounded<&$t> for Decimal
        where
            Decimal: DivRounded<$t>,
        {
            type Output = <Decimal as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: &$t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(self, *rhs, n_frac_digits)
            }
        }

        impl DivRounded<&$t> for &Decimal
        where
            Decimal: DivRounded<$t>,
        {
            type Output = <Decimal as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: &$t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, *rhs, n_frac_digits)
            }
        }

        impl DivRounded<Decimal> for $t {
            type Output = Decimal;

            fn div_rounded(self, rhs: Decimal, n_frac_digits: u8) -> Self::Output {
                if rhs.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self == 0 {
                    return Decimal::ZERO;
                }
                if let Some(coeff) = checked_div_rounded(
                    i128::from(self),
                    0_u8,
                    rhs.coeff,
                    rhs.n_frac_digits,
                    n_frac_digits,
                ) {
                    Self::Output {
                        coeff,
                        n_frac_digits,
                    }
                } else {
                    panic!("{}", DecimalError::InternalOverflow);
                }
            }
        }

        impl<'a> DivRounded<Decimal> for &'a $t
        where
            $t: DivRounded<Decimal>,
        {
            type Output = <$t as DivRounded<Decimal>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: Decimal, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, rhs, n_frac_digits)
            }
        }

        impl DivRounded<&Decimal> for $t
        where
            $t: DivRounded<Decimal>,
        {
            type Output = <$t as DivRounded<Decimal>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: &Decimal, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(self, *rhs, n_frac_digits)
            }
        }

        impl DivRounded<&Decimal> for &$t
        where
            $t: DivRounded<Decimal>,
        {
            type Output = <$t as DivRounded<Decimal>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: &Decimal, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, *rhs, n_frac_digits)
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
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = (&d).div_rounded(i, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = d.div_rounded(&i, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = (&d).div_rounded(&i, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
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

    #[test]
    fn test_div_rounded_decimal_zero_by_int() {
        let x = Decimal::new_raw(0, 3);
        let y = 123_i64;
        let z = x.div_rounded(y, 2);
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_div_rounded_int_zero_by_decimal() {
        let x = 0_u32;
        let y = Decimal::new_raw(1234567, 3);
        let z = x.div_rounded(y, 13);
        assert_eq!(z.coefficient(), 0);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_div_rounded_decimal_by_int_one() {
        let x = Decimal::new_raw(17, 5);
        let y = 1_i64;
        let z = x.div_rounded(y, 5);
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 5);
        let y = 1_u8;
        let z = x.div_rounded(y, 7);
        assert_eq!(z.coefficient(), 1700);
        assert_eq!(z.n_frac_digits(), 7);
        let y = 1_i32;
        let z = x.div_rounded(y, 4);
        assert_eq!(z.coefficient(), 2);
        assert_eq!(z.n_frac_digits(), 4);
    }

    #[test]
    fn test_div_rounded_int_by_decimal_one() {
        let x = 17;
        let y = Decimal::ONE;
        let z: Decimal = x.div_rounded(y, 0);
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 0);
        let x = 1_u64;
        let y = Decimal::new_raw(1000, 3);
        let z = x.div_rounded(y, 2);
        assert_eq!(z.coefficient(), 100);
        assert_eq!(z.n_frac_digits(), 2);
    }

    // corner case: shifting divident overflows, stepwise algorithm must be
    // used
    #[test]
    #[allow(clippy::integer_division)]
    fn test_div_rounded_stepwise() {
        let x = Decimal::new_raw(i128::MAX, 0);
        let y = Decimal::new_raw(20, 0);
        let z = x.div_rounded(y, 1);
        assert_eq!(z.coefficient(), (i128::MAX / 20) * 10 + 4);
        assert_eq!(z.n_frac_digits(), 1);
    }

    #[test]
    #[should_panic]
    fn test_div_rounded_decimal_by_int_zero() {
        let x = Decimal::new_raw(17, 3);
        let y = 0_i64;
        let _z = x.div_rounded(y, 5);
    }
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
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = (&i).div_rounded(d, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = i.div_rounded(&d, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = (&i).div_rounded(&d, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
            }
        };
    }

    gen_div_rounded_int_by_decimal_tests!(test_u8, 2, -14, 3_u8, 5, -2142857);
    gen_div_rounded_int_by_decimal_tests!(test_i8, 0, -12, -3_i8, 5, 25000);
    gen_div_rounded_int_by_decimal_tests!(
        test_u16, 2, -17, 3_u16, 5, -1764706
    );
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

    #[test]
    #[should_panic]
    fn test_div_rounded_int_by_decimal_zero() {
        let x = 17_u16;
        let y = Decimal::ZERO;
        let _z = x.div_rounded(y, 5);
    }

    #[test]
    #[should_panic]
    fn test_div_rounded_int_by_decimal_non_normalized_zero() {
        let x = -729_i32;
        let y = Decimal::new_raw(0, 3);
        let _z = x.div_rounded(y, 5);
    }
}

macro_rules! impl_div_rounded_int_and_int {
    () => {
        impl_div_rounded_int_and_int!(
            u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    ($($t:ty),*) => {
        $(
        impl DivRounded<$t> for $t {
            type Output = Decimal;

            fn div_rounded(self, rhs: $t, n_frac_digits: u8) -> Self::Output {
                if rhs == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self == 0 {
                    return Decimal::ZERO;
                }
                if let Some(coeff) = checked_div_rounded(
                    i128::from(self),
                    0_u8,
                    i128::from(rhs),
                    0_u8,
                    n_frac_digits,
                ) {
                    Self::Output {
                        coeff,
                        n_frac_digits,
                    }
                } else {
                    panic!("{}", DecimalError::InternalOverflow);
                }
            }
        }

        impl<'a> DivRounded<$t> for &'a $t
        where
            $t: DivRounded<$t>,
        {
            type Output = <$t as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: $t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, rhs, n_frac_digits)
            }
        }

        impl DivRounded<&$t> for $t
        where
            $t: DivRounded<$t>,
        {
            type Output = <$t as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: &$t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(self, *rhs, n_frac_digits)
            }
        }

        impl DivRounded<&$t> for &$t
        where
            $t: DivRounded<$t>,
        {
            type Output = <$t as DivRounded<$t>>::Output;

            #[inline(always)]
            fn div_rounded(self, rhs: &$t, n_frac_digits: u8) -> Self::Output {
                DivRounded::div_rounded(*self, *rhs, n_frac_digits)
            }
        }
        )*
    }
}

impl_div_rounded_int_and_int!();

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod div_rounded_int_by_int_tests {
    use super::*;

    macro_rules! gen_div_rounded_int_by_int_tests {
        ($func:ident, $i:expr, $j:expr, $r:expr,
         $res_coeff:expr) => {
            #[test]
            #[allow(clippy::decimal_literal_representation)]
            fn $func() {
                let i = $i;
                let j = $j;
                let r = i.div_rounded(j, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = (&i).div_rounded(j, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = i.div_rounded(&j, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
                let r = (&i).div_rounded(&j, $r);
                assert_eq!(r.coefficient(), $res_coeff);
                assert_eq!(r.n_frac_digits(), $r);
            }
        };
    }

    gen_div_rounded_int_by_int_tests!(test_u8, 44_u8, 3_u8, 5, 1466667);
    gen_div_rounded_int_by_int_tests!(test_i8, -12_i8, -3_i8, 4, 40000);
    gen_div_rounded_int_by_int_tests!(test_u16, 17_u16, 4_u16, 3, 4250);
    gen_div_rounded_int_by_int_tests!(test_i16, -22, -13_i16, 7, 16923077);
    gen_div_rounded_int_by_int_tests!(
        test_u32,
        u32::MAX,
        10_u32,
        0,
        429496730
    );
    gen_div_rounded_int_by_int_tests!(test_i32, 12345_i32, -328_i32, 1, -376);
    gen_div_rounded_int_by_int_tests!(
        test_u64,
        1_u64,
        4294967295_u64,
        32,
        23283064370807973754315
    );
    gen_div_rounded_int_by_int_tests!(
        test_i64,
        i64::MIN,
        u32::MAX as i64,
        2,
        -214748364850
    );
    gen_div_rounded_int_by_int_tests!(
        test_i128,
        987654321987654321_i128,
        1234567890_i128,
        1,
        8000000081
    );

    #[test]
    #[should_panic]
    fn test_div_rounded_int_by_int_zero() {
        let x = 17_u16;
        let y = 0_u16;
        let _z = x.div_rounded(y, 5);
    }
}
