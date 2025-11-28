// ---------------------------------------------------------------------------
// Copyright:   (c) 2022 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#[cfg(feature = "std")]
use core::cell::RefCell;

use crate::{
    i128_div_mod_floor, i128_shifted_div_mod_floor, i256_div_mod_floor,
    ten_pow,
};

/// Enum representing the different methods used when rounding a number.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

#[cfg(feature = "std")]
thread_local!(
    static DFLT_ROUNDING_MODE: RefCell<RoundingMode> =
        const { RefCell::new(RoundingMode::RoundHalfEven) }
);

#[cfg(feature = "std")]
impl Default for RoundingMode {
    /// Returns the default RoundingMode set for the current thread.
    ///
    /// It is initially set to [RoundingMode::RoundHalfEven], but can be
    /// changed using the fn [RoundingMode::set_default].
    fn default() -> Self {
        DFLT_ROUNDING_MODE.with(|m| *m.borrow())
    }
}

#[cfg(feature = "std")]
impl RoundingMode {
    /// Sets the default RoundingMode for the current thread.
    pub fn set_default(mode: Self) {
        DFLT_ROUNDING_MODE.with(|m| *m.borrow_mut() = mode);
    }
}

#[cfg(not(feature = "std"))]
static DFLT_ROUNDING_MODE: RoundingMode = RoundingMode::RoundHalfEven;

#[cfg(not(feature = "std"))]
impl Default for RoundingMode {
    /// Returns the current default RoundingMode.
    ///
    /// It is initially set to [RoundingMode::RoundHalfEven], but can be
    /// changed using the fn [RoundingMode::set_default].
    fn default() -> Self {
        DFLT_ROUNDING_MODE
    }
}

/// Rounding a number to a given number of fractional digits.
pub trait Round
where
    Self: Sized,
{
    /// Returns a new `Self` instance with its value rounded to
    /// `n_frac_digits` fractional digits according to the current
    /// [RoundingMode].
    fn round(self, n_frac_digits: i8) -> Self;

    /// Returns a new `Self` instance with its value rounded to
    /// `n_frac_digits` fractional digits according to the current
    /// `RoundingMode`, wrapped in `Option::Some`, or `Option::None` if
    /// the result can not be represented by `Self`.
    fn checked_round(self, n_frac_digits: i8) -> Option<Self>;
}

// rounding helper

// Round `quot` according to `mode` based on `rem` and `divisor`.
// Pre-condition: 0 < divisor and rem <= divisor
#[inline]
fn round_quot(
    quot: i128,
    rem: u128,
    divisor: u128,
    mode: Option<RoundingMode>,
) -> i128 {
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
            // quotient not negativ and quotient divisible by 5 w/o remainder
            // or quotient negativ and (quotient + 1) not
            // divisible by 5 w/o rem. => add 1
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
            if rem_doubled > divisor
                || rem_doubled == divisor && quot % 2 != 0
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

/// Divide 'divident' by 'divisor' and round result according to 'mode'.
#[doc(hidden)]
#[must_use]
pub fn i128_div_rounded(
    mut divident: i128,
    mut divisor: i128,
    mode: Option<RoundingMode>,
) -> i128 {
    if divisor < 0 {
        divident = -divident;
        divisor = -divisor;
    }
    let (quot, rem) = i128_div_mod_floor(divident, divisor);
    // div_mod_floor with divisor > 0 => rem >= 0
    round_quot(quot, rem as u128, divisor as u128, mode)
}

/// Divide 'divident * 10^p' by 'divisor' and round result according to
/// 'mode'.
#[doc(hidden)]
#[must_use]
pub fn i128_shifted_div_rounded(
    mut divident: i128,
    p: u8,
    mut divisor: i128,
    mode: Option<RoundingMode>,
) -> Option<i128> {
    if divisor < 0 {
        divident = -divident;
        divisor = -divisor;
    }
    let (quot, rem) = i128_shifted_div_mod_floor(divident, p, divisor)?;
    // div_mod_floor with divisor > 0 => rem >= 0
    Some(round_quot(quot, rem as u128, divisor as u128, mode))
}

/// Divide 'x * y' by '10^p' and round result according to 'mode'.
#[doc(hidden)]
#[must_use]
pub fn i128_mul_div_ten_pow_rounded(
    x: i128,
    y: i128,
    p: u8,
    mode: Option<RoundingMode>,
) -> Option<i128> {
    let divisor = ten_pow(p);
    let (quot, rem) = i256_div_mod_floor(x, y, divisor)?;
    // div_mod_floor with divisor > 0 => rem >= 0
    Some(round_quot(quot, rem as u128, divisor as u128, mode))
}

#[cfg(feature = "std")]
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
            let quot = i128_div_rounded(divident, divisor, Some(rnd_mode));
            assert_eq!(quot, result);
        }
    }
}
