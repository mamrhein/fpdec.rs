// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::cmp::Ordering;

use fpdec_core::ten_pow;

use crate::{rounding::div_i128_rounded, Decimal};

/// Multiplication giving a result rounded to a given number of fractional
/// digits.
pub trait MulRounded<Rhs = Self> {
    /// The resulting type after applying `mul_rounded`.
    type Output;

    /// Returns `self` * `rhs`, rounded to `n_frac_digits`.
    fn mul_rounded(self, rhs: Rhs, n_frac_digits: u8) -> Self::Output;
}

impl MulRounded<Decimal> for Decimal {
    type Output = Self;

    #[inline]
    fn mul_rounded(self, rhs: Decimal, n_frac_digits: u8) -> Self::Output {
        let max_n_frac_digits = self.n_frac_digits + rhs.n_frac_digits;
        match n_frac_digits.cmp(&(max_n_frac_digits)) {
            Ordering::Less => Self::Output {
                coeff: div_i128_rounded(
                    self.coeff * rhs.coeff,
                    ten_pow(max_n_frac_digits - n_frac_digits),
                    None,
                ),
                n_frac_digits,
            },
            // no need for rounding
            _ => Self::Output {
                coeff: self.coeff * rhs.coeff,
                n_frac_digits: max_n_frac_digits,
            },
        }
    }
}

forward_ref_binop_rounded!(impl MulRounded, mul_rounded);

#[cfg(test)]
mod mul_rounded_decimal_tests {
    use super::*;

    #[test]
    fn test_mul_rounded_less_n_frac_digits() {
        let x = Decimal::new_raw(12345, 2);
        let z = x.mul_rounded(x, 2);
        assert_eq!(z.coefficient(), 1523990);
        assert_eq!(z.n_frac_digits(), 2);
        let y = Decimal::new_raw(5781, 4);
        let z = x.mul_rounded(y, 1);
        assert_eq!(z.coefficient(), 714);
        assert_eq!(z.n_frac_digits(), 1);
        let z = y.mul_rounded(x, 1);
        assert_eq!(z.coefficient(), 714);
        assert_eq!(z.n_frac_digits(), 1);
    }

    #[test]
    fn test_mul_rounded_no_adj_needed() {
        let x = Decimal::new_raw(12345, 2);
        let z = x.mul_rounded(x, 4);
        assert_eq!(z.coefficient(), 152399025);
        assert_eq!(z.n_frac_digits(), 4);
        let y = Decimal::new_raw(5781, 4);
        let z = x.mul_rounded(y, 10);
        assert_eq!(z.coefficient(), 71366445);
        assert_eq!(z.n_frac_digits(), 6);
        let z = y.mul_rounded(x, 7);
        assert_eq!(z.coefficient(), 71366445);
        assert_eq!(z.n_frac_digits(), 6);
    }

    #[test]
    fn test_mul_rounded_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x.mul_rounded(y, 2);
        let a = MulRounded::mul_rounded(&x, y, 2);
        assert_eq!(a.coefficient(), z.coefficient());
        let a = MulRounded::mul_rounded(x, &y, 2);
        assert_eq!(a.coefficient(), z.coefficient());
        let a = MulRounded::mul_rounded(&x, &y, 2);
        assert_eq!(a.coefficient(), z.coefficient());
    }
}
