// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![doc = include_str ! ("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(dead_code)]
#![warn(missing_docs)]

#[doc(inline)]
pub use as_integer_ratio::AsIntegerRatio;
#[doc(inline)]
pub use binops::{
    checked_add_sub::CheckedAdd, checked_add_sub::CheckedSub,
    checked_div::CheckedDiv, checked_mul::CheckedMul, checked_rem::CheckedRem,
    div_rounded::DivRounded, mul_rounded::MulRounded,
};
#[doc(inline)]
pub use errors::*;
use fpdec_core::i128_magnitude;
#[doc(inline)]
pub use fpdec_core::{
    ParseDecimalError, Round, RoundingMode, MAX_N_FRAC_DIGITS,
};
#[doc(inline)]
pub use fpdec_macros::Dec;
#[doc(inline)]
pub use quantize::Quantize;

mod as_integer_ratio;
mod binops;
mod errors;
mod format;
mod from_float;
mod from_int;
mod from_str;
mod quantize;
mod round;
#[cfg(feature = "num-traits")]
mod traits;
mod unops;

/// Represents a decimal number as a coefficient (`i128`) combined with a
/// value (`u8`) specifying the number of fractional decimal digits.
///
/// The number of fractional digits can be in the range 0 ..
/// [`MAX_N_FRAC_DIGITS`].
#[derive(Copy, Clone)]
#[cfg_attr(feature = "packed", repr(packed))]
pub struct Decimal {
    coeff: i128,
    n_frac_digits: u8,
}

impl Decimal {
    // needs to be public because of macro Dec!
    #[doc(hidden)]
    #[inline(always)]
    pub const fn new_raw(coeff: i128, n_frac_digits: u8) -> Self {
        debug_assert!(
            n_frac_digits <= MAX_N_FRAC_DIGITS,
            "More than MAX_N_FRAC_DIGITS fractional decimal digits requested."
        );
        Self {
            coeff,
            n_frac_digits,
        }
    }

    /// Coefficient of `self`.
    #[inline(always)]
    pub const fn coefficient(self) -> i128 {
        self.coeff
    }

    /// Number of fractional decimal digits of `self`.
    #[inline(always)]
    pub const fn n_frac_digits(self) -> u8 {
        self.n_frac_digits
    }

    /// Returns the positional index of the most significant decimal digit of
    /// `self`.
    ///
    /// Special case: for a value equal to 0 `magnitude()` returns 0.
    ///
    /// # Examples:
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal};
    /// let d = Dec!(123);
    /// assert_eq!(d.magnitude(), 2);
    /// let d = Dec!(0.00123);
    /// assert_eq!(d.magnitude(), -3);
    /// let d = Decimal::ZERO;
    /// assert_eq!(d.magnitude(), 0);
    #[inline(always)]
    pub fn magnitude(self) -> i8 {
        i128_magnitude(self.coeff) as i8 - self.n_frac_digits as i8
    }

    /// Additive identity
    pub const ZERO: Decimal = Decimal {
        coeff: 0,
        n_frac_digits: 0,
    };

    /// Multiplicative identity
    pub const ONE: Decimal = Decimal {
        coeff: 1,
        n_frac_digits: 0,
    };

    /// Multiplicative negator
    pub const NEG_ONE: Decimal = Decimal {
        coeff: -1,
        n_frac_digits: 0,
    };

    /// Equivalent of 2
    pub const TWO: Decimal = Decimal {
        coeff: 2,
        n_frac_digits: 0,
    };

    /// Equivalent of 10
    pub const TEN: Decimal = Decimal {
        coeff: 10,
        n_frac_digits: 0,
    };

    /// Maximum value representable by `Decimal`
    pub const MAX: Decimal = Decimal {
        coeff: i128::MAX,
        n_frac_digits: 0,
    };

    /// Minimum value representable by `Decimal`
    pub const MIN: Decimal = Decimal {
        coeff: i128::MIN,
        n_frac_digits: 0,
    };

    /// Smallest absolute difference between two non-equal values of `Decimal`
    pub const DELTA: Decimal = Decimal {
        coeff: 1i128,
        n_frac_digits: MAX_N_FRAC_DIGITS,
    };
}

impl Default for Decimal {
    /// Default value: Decimal::ZERO
    #[inline(always)]
    fn default() -> Self {
        Self::ZERO
    }
}

#[inline]
pub(crate) fn normalize(coeff: &mut i128, n_frac_digits: &mut u8) {
    if *coeff == 0 {
        *n_frac_digits = 0;
    } else {
        // eliminate trailing zeros in coeff
        while *coeff % 10 == 0 && *n_frac_digits > 0 {
            *coeff /= 10;
            *n_frac_digits -= 1;
        }
    }
}
