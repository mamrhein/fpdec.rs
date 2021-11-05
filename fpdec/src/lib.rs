// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![doc = include_str ! ("../../README.md")]
#![allow(dead_code)]
#![warn(missing_docs)]

#[doc(inline)]
pub use fpdec_core::{ParseDecimalError, MAX_PRECISION};
#[doc(inline)]
pub use fpdec_macros::Dec;

/// Represents a decimal number as a coefficient (`i128`) combined with a
/// precision (`u8`) specifying the number of fractional decimal digits.
///
/// The precision can be in the range 0 .. [`MAX_PRECISION`].
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
}
