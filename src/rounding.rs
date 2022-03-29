// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use std::cell::RefCell;

use fpdec_core::{div_mod_floor, ten_pow};

use crate::Decimal;

/// Enum representiong the different methods used when rounding a `Decimal`
/// value.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RoundingMode {
    /// Round away from zero if last digit after rounding towards zero would
    /// have been 0 or 5; otherwise round towards zero.
    Round05Up,
    /// Round towards Infinity.
    RoundCeiling,
    /// Round towards zero.
    RoundDown,
    /// Round towards -Infinity.
    RoundFloor,
    /// Round to nearest with ties going towards zero.
    RoundHalfDown,
    /// Round to nearest with ties going to nearest even integer.
    RoundHalfEven,
    /// Round to nearest with ties going away from zero.
    RoundHalfUp,
    /// Round away from zero.
    RoundUp,
}

thread_local!(
    static DFLT_ROUNDING_MODE: RefCell<RoundingMode> =
        RefCell::new(RoundingMode::RoundHalfEven)
);

impl Default for RoundingMode {
    /// Returns the default RoundingMode set for the current thread.
    ///
    /// It is initially set to [RoundingMode::RoundHalfEven], but can be changed
    /// using the fn [RoundingMode::set_default].
    fn default() -> Self {
        DFLT_ROUNDING_MODE.with(|m| *m.borrow())
    }
}

impl RoundingMode {
    /// Sets the default RoundingMode for the current thread.
    pub fn set_default(mode: RoundingMode) {
        DFLT_ROUNDING_MODE.with(|m| *m.borrow_mut() = mode)
    }
}

/// Rounding a number to a given number of fractional digits.
pub trait Round
where
    Self: Sized,
{
    /// Returns a new `Self` instance with its value rounded to `n_frac_digits`
    /// fractional digits according to the current [RoundingMode].
    fn round(self, n_frac_digits: i8) -> Self;

    /// Returns a new `Self` instance with its value rounded to `n_frac_digits`
    /// fractional digits according to the current `RoundingMode`, wrapped in
    /// `Option::Some`, or `Option::None` if the result can not be
    /// represented by `Self`.
    fn checked_round(self, n_frac_digits: i8) -> Option<Self>;
}

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

// rounding helper

/// Divide 'divident' by 'divisor' and round result according to 'mode'.
pub(crate) fn div_i128_rounded(
    mut divident: i128,
    mut divisor: i128,
    mode: Option<RoundingMode>,
) -> i128 {
    if divisor < 0 {
        divident = -divident;
        divisor = -divisor;
    }
    let (quot, rem) = div_mod_floor(divident, divisor);
    // div_mod_floor with divisor > 0 => rem >= 0
    if rem == 0 {
        // no need for rounding
        return quot;
    }
    // here: |divisor| >= 2 => rem <= |divident| / 2,
    // therefor it's safe to use rem << 1
    let mode = match mode {
        None => RoundingMode::default(),
        Some(mode) => mode,
    };
    match mode {
        RoundingMode::Round05Up => {
            // Round down unless last digit is 0 or 5:
            // quotient not negativ and quotient divisible by 5 w/o remainder or
            // quotient negativ and (quotient + 1) not divisible by 5 w/o rem.
            // => add 1
            if quot >= 0 && quot % 5 == 0 || quot < 0 && (quot + 1) % 5 != 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundCeiling => {
            // Round towards Infinity (i. e. not away from 0 if negative):
            // => always add 1
            return quot + 1;
        }
        RoundingMode::RoundDown => {
            // Round towards 0 (aka truncate):
            // quotient negativ => add 1
            if quot < 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundFloor => {
            // Round towards -Infinity (i.e. not towards 0 if negative):
            // => never add 1
            return quot;
        }
        RoundingMode::RoundHalfDown => {
            // Round 5 down, rest to nearest:
            // remainder > |divisor| / 2 or
            // remainder = |divisor| / 2 and quotient < 0
            // => add 1
            let rem_doubled = rem << 1;
            if rem_doubled > divisor || rem_doubled == divisor && quot < 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundHalfEven => {
            // Round 5 to nearest even, rest to nearest:
            // remainder > |divisor| / 2 or
            // remainder = |divisor| / 2 and quotient not even
            // => add 1
            let rem_doubled = rem << 1;
            if rem_doubled > divisor || rem_doubled == divisor && quot % 2 != 0
            {
                return quot + 1;
            }
        }
        RoundingMode::RoundHalfUp => {
            // Round 5 up (away from 0), rest to nearest:
            // remainder > |divisor| / 2 or
            // remainder = |divisor| / 2 and quotient >= 0
            // => add 1
            let rem_doubled = rem << 1;
            if rem_doubled > divisor || rem_doubled == divisor && quot >= 0 {
                return quot + 1;
            }
        }
        RoundingMode::RoundUp => {
            // Round away from 0:
            // quotient not negative => add 1
            if quot >= 0 {
                return quot + 1;
            }
        }
    }
    // fall-through: round towards 0
    quot
}

#[cfg(test)]
mod rounding_mode_tests {
    use super::*;

    #[test]
    fn test1() {
        assert_eq!(RoundingMode::default(), RoundingMode::RoundHalfEven);
        RoundingMode::set_default(RoundingMode::RoundUp);
        assert_eq!(RoundingMode::default(), RoundingMode::RoundUp);
        RoundingMode::set_default(RoundingMode::RoundHalfEven);
        assert_eq!(RoundingMode::default(), RoundingMode::RoundHalfEven);
    }

    #[test]
    fn test2() {
        assert_eq!(RoundingMode::default(), RoundingMode::RoundHalfEven);
        RoundingMode::set_default(RoundingMode::RoundHalfUp);
        assert_eq!(RoundingMode::default(), RoundingMode::RoundHalfUp);
        RoundingMode::set_default(RoundingMode::RoundHalfEven);
        assert_eq!(RoundingMode::default(), RoundingMode::RoundHalfEven);
    }
}

#[cfg(test)]
mod helper_tests {
    use super::*;

    const TESTDATA: [(i128, i128, RoundingMode, i128); 34] = [
        (17, 5, RoundingMode::Round05Up, 3),
        (27, 5, RoundingMode::Round05Up, 6),
        (-17, 5, RoundingMode::Round05Up, -3),
        (-27, 5, RoundingMode::Round05Up, -6),
        (17, 5, RoundingMode::RoundCeiling, 4),
        (15, 5, RoundingMode::RoundCeiling, 3),
        (-17, 5, RoundingMode::RoundCeiling, -3),
        (-15, 5, RoundingMode::RoundCeiling, -3),
        (19, 5, RoundingMode::RoundDown, 3),
        (15, 5, RoundingMode::RoundDown, 3),
        (-18, 5, RoundingMode::RoundDown, -3),
        (-15, 5, RoundingMode::RoundDown, -3),
        (19, 5, RoundingMode::RoundFloor, 3),
        (15, 5, RoundingMode::RoundFloor, 3),
        (-18, 5, RoundingMode::RoundFloor, -4),
        (-15, 5, RoundingMode::RoundFloor, -3),
        (19, 2, RoundingMode::RoundHalfDown, 9),
        (15, 4, RoundingMode::RoundHalfDown, 4),
        (-19, 2, RoundingMode::RoundHalfDown, -9),
        (-15, 4, RoundingMode::RoundHalfDown, -4),
        (19, 2, RoundingMode::RoundHalfEven, 10),
        (15, 4, RoundingMode::RoundHalfEven, 4),
        (-225, 50, RoundingMode::RoundHalfEven, -4),
        (-15, 4, RoundingMode::RoundHalfEven, -4),
        (
            u64::MAX as i128,
            i64::MIN as i128 * 10,
            RoundingMode::RoundHalfEven,
            0,
        ),
        (19, 2, RoundingMode::RoundHalfUp, 10),
        (10802, 4321, RoundingMode::RoundHalfUp, 2),
        (-19, 2, RoundingMode::RoundHalfUp, -10),
        (-10802, 4321, RoundingMode::RoundHalfUp, -2),
        (19, 2, RoundingMode::RoundUp, 10),
        (10802, 4321, RoundingMode::RoundUp, 3),
        (-19, 2, RoundingMode::RoundUp, -10),
        (-10802, 4321, RoundingMode::RoundUp, -3),
        (i32::MAX as i128, 1, RoundingMode::RoundUp, i32::MAX as i128),
    ];

    #[test]
    fn test_div_rounded() {
        for (divident, divisor, rnd_mode, result) in TESTDATA {
            let quot = div_i128_rounded(divident, divisor, Some(rnd_mode));
            // println!("{} {} {:?}", divident, divisor, rnd_mode);
            assert_eq!(quot, result);
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
        assert_eq!(x.coeff, y.coeff);
        assert_eq!(x.n_frac_digits, y.n_frac_digits);
        let y = x.checked_round(5).unwrap();
        assert_eq!(x.coeff, y.coeff);
        assert_eq!(x.n_frac_digits, y.n_frac_digits);
    }

    #[test]
    fn test_decimal_round_result_zero() {
        let x = Decimal::new_raw(12345, 2);
        let y = x.round(-3);
        assert_eq!(y.coeff, 0);
        assert_eq!(y.n_frac_digits, 0);
        let y = x.round(-37);
        assert_eq!(y.coeff, 0);
        assert_eq!(y.n_frac_digits, 0);
        let y = x.checked_round(-9).unwrap();
        assert_eq!(y.coeff, 0);
        assert_eq!(y.n_frac_digits, 0);
        let y = x.checked_round(-42).unwrap();
        assert_eq!(y.coeff, 0);
        assert_eq!(y.n_frac_digits, 0);
    }

    #[test]
    fn test_decimal_round() {
        let d = Decimal::new_raw(12345, 0);
        assert_eq!(d.round(-1).coeff, 12340);
        let d = Decimal::new_raw(1285, 0);
        assert_eq!(d.round(-2).coeff, 1300);
        let d = Decimal::new_raw(12345, 1);
        assert_eq!(d.round(0).coeff, 1234);
        let d = Decimal::new_raw(1285, 2);
        assert_eq!(d.round(0).coeff, 13);
        let d = Decimal::new_raw(12345678909876543, 7);
        assert_eq!(d.round(0).coeff, 1234567891);
        let d = Decimal::new_raw(123455, 9);
        assert_eq!(d.round(8).coeff, 12346);
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
        assert_eq!(d.checked_round(-1).unwrap().coeff, 12340);
        let d = Decimal::new_raw(1285, 0);
        assert_eq!(d.checked_round(-2).unwrap().coeff, 1300);
        let d = Decimal::new_raw(12345, 1);
        assert_eq!(d.checked_round(0).unwrap().coeff, 1234);
        let d = Decimal::new_raw(1285, 2);
        assert_eq!(d.checked_round(0).unwrap().coeff, 13);
        let d = Decimal::new_raw(12345678909876543, 7);
        assert_eq!(d.checked_round(0).unwrap().coeff, 1234567891);
        let d = Decimal::new_raw(123455, 9);
        assert_eq!(d.checked_round(8).unwrap().coeff, 12346);
        let d = Decimal::new_raw(170141183460469231731687303715884105727, 0);
        let res = d.checked_round(-1);
        assert!(res.is_none());
        let d = Decimal::new_raw(170141183460469231731687303715884105727, 0);
        let res = d.checked_round(-1);
        assert!(res.is_none());
    }
}
