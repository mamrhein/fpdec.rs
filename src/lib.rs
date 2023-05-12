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
// activate some rustc lints
#![deny(non_ascii_idents)]
#![deny(unsafe_code)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused)]
#![allow(dead_code)]
// activate some clippy lints
#![warn(clippy::cast_possible_truncation)]
// #![warn(clippy::cast_possible_wrap)]
#![warn(clippy::cast_precision_loss)]
// #![warn(clippy::cast_sign_loss)]
#![warn(clippy::cognitive_complexity)]
#![warn(clippy::decimal_literal_representation)]
#![warn(clippy::enum_glob_use)]
#![warn(clippy::equatable_if_let)]
#![warn(clippy::fallible_impl_from)]
#![warn(clippy::if_not_else)]
#![warn(clippy::if_then_some_else_none)]
#![warn(clippy::implicit_clone)]
#![warn(clippy::integer_division)]
#![warn(clippy::manual_assert)]
#![warn(clippy::match_same_arms)]
// #![warn(clippy::mismatching_type_param_order)] TODO: enable when 1.62 stable
#![warn(clippy::missing_const_for_fn)]
#![warn(clippy::missing_errors_doc)]
#![warn(clippy::missing_panics_doc)]
#![warn(clippy::multiple_crate_versions)]
// #![warn(clippy::multiple_inherent_impl)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::needless_pass_by_value)]
#![warn(clippy::print_stderr)]
#![warn(clippy::print_stdout)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::unicode_not_nfc)]
#![warn(clippy::unimplemented)]
#![warn(clippy::unseparated_literal_suffix)]
#![warn(clippy::unused_self)]
#![warn(clippy::unwrap_in_result)]
#![warn(clippy::use_self)]
#![warn(clippy::used_underscore_binding)]
#![warn(clippy::wildcard_imports)]

extern crate alloc;

#[cfg(feature = "serde-as-str")]
use alloc::string::String;

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
#[must_use]
#[derive(Copy, Clone)]
#[cfg_attr(
    feature = "serde-as-str",
    derive(serde::Serialize, serde::Deserialize)
)]
#[cfg_attr(
    feature = "serde-as-str",
    serde(into = "String"),
    serde(try_from = "String")
)]
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
    #[must_use]
    #[inline(always)]
    pub const fn coefficient(self) -> i128 {
        self.coeff
    }

    /// Number of fractional decimal digits of `self`.
    #[must_use]
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
    #[must_use]
    #[inline(always)]
    pub const fn magnitude(self) -> i8 {
        i128_magnitude(self.coeff) as i8 - self.n_frac_digits as i8
    }

    /// Additive identity
    pub const ZERO: Self = Self {
        coeff: 0,
        n_frac_digits: 0,
    };

    /// Multiplicative identity
    pub const ONE: Self = Self {
        coeff: 1,
        n_frac_digits: 0,
    };

    /// Multiplicative negator
    pub const NEG_ONE: Self = Self {
        coeff: -1,
        n_frac_digits: 0,
    };

    /// Equivalent of 2
    pub const TWO: Self = Self {
        coeff: 2,
        n_frac_digits: 0,
    };

    /// Equivalent of 10
    pub const TEN: Self = Self {
        coeff: 10,
        n_frac_digits: 0,
    };

    /// Maximum value representable by `Decimal` = 2¹²⁷ - 1
    pub const MAX: Self = Self {
        coeff: i128::MAX,
        n_frac_digits: 0,
    };

    /// Minimum value representable by `Decimal`  = -2¹²⁷ + 1
    pub const MIN: Self = Self {
        coeff: i128::MIN + 1,
        n_frac_digits: 0,
    };

    /// Smallest absolute difference between two non-equal values of `Decimal`
    pub const DELTA: Self = Self {
        coeff: 1_i128,
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

#[cfg(feature = "serde-as-str")]
#[cfg(test)]
mod serde_json_tests {
    use serde_json;

    use super::*;

    #[test]
    fn test_min() {
        let d = Decimal::MIN;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_neg_one() {
        let d = Decimal::NEG_ONE;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_zero() {
        let d = Decimal::ZERO;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_delta() {
        let d = Decimal::DELTA;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_some() {
        let d = Dec!(123456789012345678.90123);
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_max() {
        let d = Decimal::MAX;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }
}
