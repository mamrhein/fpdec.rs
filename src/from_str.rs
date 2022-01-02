// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{convert::TryFrom, str::FromStr};

use fpdec_core::{checked_mul_pow_ten, dec_repr_from_str};

use crate::{Decimal, ParseDecimalError, MAX_N_FRAC_DIGITS};

impl FromStr for Decimal {
    type Err = ParseDecimalError;

    /// Convert a number literal into a `Decimal`.
    ///
    /// The literal must be in the form
    ///
    /// `[+|-]<int>[.<frac>][<e|E>[+|-]<exp>]`
    ///
    /// or
    ///
    /// `[+|-].<frac>[<e|E>[+|-]<exp>]`.
    ///
    /// The function returns an error in these cases:
    ///
    /// * An empty string has been given as `lit` -> `ParseDecimalError::Empty`
    /// * `lit` does not fit one of the two forms given above ->
    ///   `ParseDecimalError::Invalid`
    /// * The number of fractional digits in `lit` minus the value of the signed
    ///   exponent in `lit` exceeds [crate::MAX_N_FRAC_DIGITS] ->
    ///   `ParseDecimalError::FracDigitLimitExceeded`
    /// * The given decimal literal exceeds the the internal representation of
    ///   `Decimal`. -> ParseDecimalError::InternalOverflow
    ///
    /// # Examples:
    ///
    /// ```rust
    /// # use fpdec::{Decimal, ParseDecimalError};
    /// # use core::str::FromStr;
    /// # fn main() -> Result<(), ParseDecimalError> {
    /// let d = Decimal::from_str("38.207")?;
    /// assert_eq!(d.to_string(), "38.207");
    /// let d = Decimal::from_str("-132.02070e-2")?;
    /// assert_eq!(d.to_string(), "-1.3202070");
    /// # Ok(()) }
    /// ```
    fn from_str(lit: &str) -> Result<Self, Self::Err> {
        let (coeff, exponent) = dec_repr_from_str(lit)?;
        if -exponent > MAX_N_FRAC_DIGITS as isize {
            return Result::Err(ParseDecimalError::FracDigitLimitExceeded);
        }
        if exponent > 38 {
            // 10 ^ 39 > int128::MAX
            return Result::Err(ParseDecimalError::InternalOverflow);
        }
        if exponent < 0 {
            Ok(Self {
                coeff,
                n_frac_digits: -exponent as u8,
            })
        } else {
            match checked_mul_pow_ten(coeff, exponent as u8) {
                None => Result::Err(ParseDecimalError::InternalOverflow),
                Some(coeff) => Ok(Self {
                    coeff,
                    n_frac_digits: 0,
                }),
            }
        }
    }
}

impl TryFrom<&str> for Decimal {
    type Error = ParseDecimalError;

    #[inline]
    fn try_from(lit: &str) -> Result<Self, Self::Error> {
        Self::from_str(lit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_int_lit() {
        let d = Decimal::from_str("1957945").unwrap();
        assert_eq!(d.coefficient(), 1957945);
        assert_eq!(d.n_frac_digits(), 0);
    }

    #[test]
    fn test_from_dec_lit() {
        let d = Decimal::from_str("-17.5").unwrap();
        assert_eq!(d.coefficient(), -175);
        assert_eq!(d.n_frac_digits(), 1);
    }

    #[test]
    fn test_from_frac_only_lit() {
        let d = Decimal::from_str("+.75").unwrap();
        assert_eq!(d.coefficient(), 75);
        assert_eq!(d.n_frac_digits(), 2);
    }

    #[test]
    fn test_from_int_lit_neg_exp() {
        let d = Decimal::from_str("17e-5").unwrap();
        assert_eq!(d.coefficient(), 17);
        assert_eq!(d.n_frac_digits(), 5);
    }

    #[test]
    fn test_from_int_lit_pos_exp() {
        let d = Decimal::from_str("+217e3").unwrap();
        assert_eq!(d.coefficient(), 217000);
        assert_eq!(d.n_frac_digits(), 0);
    }

    #[test]
    fn test_from_dec_lit_neg_exp() {
        let d = Decimal::from_str("-533.7e-2").unwrap();
        assert_eq!(d.coefficient(), -5337);
        assert_eq!(d.n_frac_digits(), 3);
    }

    #[test]
    fn test_from_dec_lit_pos_exp() {
        let d = Decimal::from_str("700004.002E13").unwrap();
        assert_eq!(d.coefficient(), 7000040020000000000);
        assert_eq!(d.n_frac_digits(), 0);
    }

    #[test]
    fn test_err_empty_str() {
        let res = Decimal::from_str("");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::Empty);
    }

    #[test]
    fn test_err_invalid_lit() {
        let lits = [" ", "+", "-4.33.2", "2.87 e3", "+e3", ".4e3 "];
        for lit in lits {
            let res = Decimal::from_str(lit);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, ParseDecimalError::Invalid);
        }
    }

    #[test]
    fn test_frac_limit_exceeded() {
        let res =
            Decimal::from_str("0.000000000000000000000000000000000000001");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_frac_limit_exceeded_with_exp() {
        let res = Decimal::from_str("17.4e-38");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_int_lit_max_val_exceeded() {
        let lit = "170141183460469231731687303715884105728"; // 2 ^ 127
        let res = Decimal::from_str(&lit);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::InternalOverflow);
    }

    #[test]
    fn test_dec_lit_max_val_exceeded() {
        let s = "123456789012345678901234567890123.4567890";
        let res = Decimal::from_str(&s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::InternalOverflow);
    }

    #[test]
    fn test_parse() {
        let s = "+00028.700";
        let res = s.parse::<Decimal>();
        assert!(!res.is_err());
        let dec = res.unwrap();
        assert_eq!(dec.coefficient(), 28700);
        assert_eq!(dec.n_frac_digits(), 3);
    }

    #[test]
    fn test_parse_frac_limit_exceeded() {
        let s = "+28.7005e-35";
        let res = s.parse::<Decimal>();
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_try_from() {
        let s = "-534000.7080";
        let res = Decimal::try_from(s);
        assert!(!res.is_err());
        let dec = res.unwrap();
        assert_eq!(dec.coefficient(), -5340007080);
        assert_eq!(dec.n_frac_digits(), 4);
    }

    #[test]
    fn test_try_from_frac_limit_exceeded() {
        let s = "+28.700500E-33";
        let res = Decimal::try_from(s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }
}
