// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![doc = include_str ! ("../README.md")]
#![allow(dead_code)]
#![warn(missing_docs)]

#[doc(inline)]
pub use errors::*;
#[doc(inline)]
pub use fpdec_core::{ParseDecimalError, MAX_PRECISION};
#[doc(inline)]
pub use fpdec_macros::Dec;
#[doc(inline)]
pub use rounding::{Round, RoundingMode};

mod binops;
mod errors;
mod format;
mod from_int;
mod from_str;
mod rounding;
#[cfg(feature = "num-traits")]
mod traits;
mod unops;

/// Represents a decimal number as a coefficient (`i128`) combined with a
/// precision (`u8`) specifying the number of fractional decimal digits.
///
/// The precision can be in the range 0 .. [`MAX_PRECISION`].
#[derive(Copy, Clone, Eq, Ord)]
#[cfg_attr(feature = "packed", repr(packed))]
pub struct Decimal {
    coeff: i128,
    n_frac_digits: u8,
}

impl Decimal {
    // needs to be public because of macro Dec!
    #[doc(hidden)]
    #[inline(always)]
    pub fn new_raw(coeff: i128, n_frac_digits: u8) -> Self {
        Self {
            coeff,
            n_frac_digits,
        }
    }

    /// Coefficient of `self`.
    #[inline(always)]
    pub fn coefficient(self) -> i128 {
        self.coeff
    }

    /// Number of fractional decimal digits of `self`.
    #[inline(always)]
    pub const fn precision(self) -> u8 {
        self.n_frac_digits
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
        n_frac_digits: MAX_PRECISION,
    };
}

impl Default for Decimal {
    /// Default value: Decimal::ZERO
    #[inline(always)]
    fn default() -> Self {
        Self::ZERO
    }
}
