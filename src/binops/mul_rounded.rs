// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use fpdec_core::{
    i128_div_rounded, i128_mul_div_ten_pow_rounded, ten_pow, MAX_N_FRAC_DIGITS,
};

use crate::{Decimal, DecimalError};

/// Multiplication giving a result rounded to a given number of fractional
/// digits.
pub trait MulRounded<Rhs = Self> {
    /// The resulting type after applying `mul_rounded`.
    type Output;

    /// Returns `self` * `rhs`, rounded to `n_frac_digits`.
    fn mul_rounded(self, rhs: Rhs, n_frac_digits: u8) -> Self::Output;
}

pub(crate) fn checked_mul_rounded(
    x: Decimal,
    y: Decimal,
    n_frac_digits: u8,
) -> Option<Decimal> {
    let max_n_frac_digits = x.n_frac_digits + y.n_frac_digits;
    if n_frac_digits >= max_n_frac_digits {
        // no need for rounding
        Some(Decimal {
            coeff: x.coeff.checked_mul(y.coeff)?,
            n_frac_digits: max_n_frac_digits,
        })
    } else {
        let shift = max_n_frac_digits - n_frac_digits;
        if let Some(coeff) = x.coeff.checked_mul(y.coeff) {
            Some(Decimal {
                coeff: i128_div_rounded(coeff, ten_pow(shift), None),
                n_frac_digits,
            })
        } else {
            let coeff =
                i128_mul_div_ten_pow_rounded(x.coeff, y.coeff, shift, None)?;
            Some(Decimal {
                coeff,
                n_frac_digits,
            })
        }
    }
}

impl MulRounded<Self> for Decimal {
    type Output = Self;

    #[inline]
    fn mul_rounded(self, rhs: Self, n_frac_digits: u8) -> Self::Output {
        #[allow(clippy::manual_assert)]
        if n_frac_digits > MAX_N_FRAC_DIGITS {
            panic!("{}", DecimalError::MaxNFracDigitsExceeded);
        }
        if self.eq_zero() || rhs.eq_zero() {
            return Self::ZERO;
        }
        if let Some(res) = checked_mul_rounded(self, rhs, n_frac_digits) {
            res
        } else {
            panic!("{}", DecimalError::InternalOverflow);
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
