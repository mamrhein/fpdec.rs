// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use crate::Decimal;
use fpdec_core::{div_i128_rounded, ten_pow, Round};

impl Round for Decimal {
    /// Returns a new `Decimal` with its value rounded to `n_frac_digits`
    /// fractional digits according to the current [RoundingMode].
    ///
    /// # Panics
    ///
    /// Panics if the resulting value can not be represented by `Decimal`!
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, Round};
    /// let d = Dec!(28.27093);
    /// let r = d.round(4);
    /// assert_eq!(r.to_string(), "28.2709");
    /// let r = d.round(1);
    /// assert_eq!(r.to_string(), "28.3");
    /// let r = d.round(0);
    /// assert_eq!(r.to_string(), "28");
    /// let r = d.round(-1);
    /// assert_eq!(r.to_string(), "30");
    /// ```
    fn round(self, n_frac_digits: i8) -> Self {
        if n_frac_digits >= self.n_frac_digits as i8 {
            self
        } else if n_frac_digits < self.n_frac_digits as i8 - 38 {
            Self::ZERO
        } else {
            // n_frac_digits < self.n_frac_digits
            let shift: u8 = (self.n_frac_digits as i8 - n_frac_digits) as u8;
            let divisor = ten_pow(shift);
            let coeff = div_i128_rounded(self.coeff, divisor, None);
            if n_frac_digits >= 0 {
                Self {
                    coeff,
                    n_frac_digits: n_frac_digits as u8,
                }
            } else {
                // shift back
                Self {
                    coeff: coeff * ten_pow(-n_frac_digits as u8),
                    n_frac_digits: 0,
                }
            }
        }
    }

    /// Returns a new `Decimal` instance with its value rounded to
    /// `n_frac_digits` fractional digits according to the current
    /// [RoundingMode], wrapped in `Option::Some`, or `Option::None` if the
    /// result can not be represented by `Decimal`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, Round};
    /// # fn main() {
    /// # fn f() -> Option<Decimal> {
    /// let d = Dec!(28.27093);
    /// let r = d.checked_round(4)?;
    /// assert_eq!(r.to_string(), "28.2709");
    /// let r = d.checked_round(0)?;
    /// assert_eq!(r.to_string(), "28");
    /// let d = Dec!(170141183460469231731687303715884105727);
    /// let r = d.checked_round(-3);
    /// assert!(r.is_none());
    /// # Option::None
    /// # } f();}
    /// ```
    fn checked_round(self, n_frac_digits: i8) -> Option<Self> {
        if n_frac_digits >= self.n_frac_digits as i8 {
            Some(self)
        } else if n_frac_digits < self.n_frac_digits as i8 - 38 {
            Some(Self::ZERO)
        } else {
            // n_frac_digits < self.n_frac_digits
            let shift: u8 = (self.n_frac_digits as i8 - n_frac_digits) as u8;
            let divisor = ten_pow(shift);
            let coeff = div_i128_rounded(self.coeff, divisor, None);
            if n_frac_digits >= 0 {
                Some(Self {
                    coeff,
                    n_frac_digits: n_frac_digits as u8,
                })
            } else {
                // shift back
                coeff
                    .checked_mul(ten_pow(-n_frac_digits as u8))
                    .map(|coeff| Self {
                        coeff,
                        n_frac_digits: 0,
                    })
            }
        }
    }
}

#[cfg(test)]
mod round_decimal_tests {
    use super::*;

    #[test]
    fn test_decimal_round_no_op() {
        let x = Decimal::new_raw(12345, 2);
        let y = x.round(3);
        assert_eq!(x.coefficient(), y.coefficient());
        assert_eq!(x.n_frac_digits(), y.n_frac_digits());
        let y = x.checked_round(5).unwrap();
        assert_eq!(x.coefficient(), y.coefficient());
        assert_eq!(x.n_frac_digits(), y.n_frac_digits());
    }

    #[test]
    fn test_decimal_round_result_zero() {
        let x = Decimal::new_raw(12345, 2);
        let y = x.round(-3);
        assert_eq!(y.coefficient(), 0);
        assert_eq!(y.n_frac_digits(), 0);
        let y = x.round(-37);
        assert_eq!(y.coefficient(), 0);
        assert_eq!(y.n_frac_digits(), 0);
        let y = x.checked_round(-9).unwrap();
        assert_eq!(y.coefficient(), 0);
        assert_eq!(y.n_frac_digits(), 0);
        let y = x.checked_round(-42).unwrap();
        assert_eq!(y.coefficient(), 0);
        assert_eq!(y.n_frac_digits(), 0);
    }

    #[test]
    fn test_decimal_round() {
        let d = Decimal::new_raw(12345, 0);
        assert_eq!(d.round(-1).coefficient(), 12340);
        let d = Decimal::new_raw(1285, 0);
        assert_eq!(d.round(-2).coefficient(), 1300);
        let d = Decimal::new_raw(12345, 1);
        assert_eq!(d.round(0).coefficient(), 1234);
        let d = Decimal::new_raw(1285, 2);
        assert_eq!(d.round(0).coefficient(), 13);
        let d = Decimal::new_raw(12345678909876543, 7);
        assert_eq!(d.round(0).coefficient(), 1234567891);
        let d = Decimal::new_raw(123455, 9);
        assert_eq!(d.round(8).coefficient(), 12346);
    }

    #[test]
    #[should_panic]
    fn test_decimal_round_overflow() {
        let d = Decimal::new_raw(170141183460469231731687303715884105727, 0);
        let _ = d.round(-8);
    }

    #[test]
    fn test_decimal_checked_round() {
        let d = Decimal::new_raw(12345, 0);
        assert_eq!(d.checked_round(-1).unwrap().coefficient(), 12340);
        let d = Decimal::new_raw(1285, 0);
        assert_eq!(d.checked_round(-2).unwrap().coefficient(), 1300);
        let d = Decimal::new_raw(12345, 1);
        assert_eq!(d.checked_round(0).unwrap().coefficient(), 1234);
        let d = Decimal::new_raw(1285, 2);
        assert_eq!(d.checked_round(0).unwrap().coefficient(), 13);
        let d = Decimal::new_raw(12345678909876543, 7);
        assert_eq!(d.checked_round(0).unwrap().coefficient(), 1234567891);
        let d = Decimal::new_raw(123455, 9);
        assert_eq!(d.checked_round(8).unwrap().coefficient(), 12346);
        let d = Decimal::new_raw(170141183460469231731687303715884105727, 0);
        let res = d.checked_round(-1);
        assert!(res.is_none());
        let d = Decimal::new_raw(170141183460469231731687303715884105727, 0);
        let res = d.checked_round(-1);
        assert!(res.is_none());
    }
}
