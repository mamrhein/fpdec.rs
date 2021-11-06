// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::fmt::{Debug, Display, Formatter};

/// An error which can be returned from converting numbers to `Decimal` or from
/// binary operators on `Decimal`.
///
/// This error is used as the error type for the [`TryFrom`] implementation of
/// `Decimal`. It is also used when the implementations of the numerical
/// operators panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecimalError {
    /// The precise result would have more than [crate::MAX_PRECISION]
    /// fractional decimal digits.
    PrecLimitExceeded,
    /// The result would exceed the internal representation of `Decimal`.
    InternalOverflow,
    /// Attempt to convert an infinite value to `Decimal`.
    InfiniteValue,
    /// Attempt to convert a 'not-a-number' value to a `Decimal`.
    NotANumber,
    /// A division op called with a divisor equal to zero.
    DivisionByZero,
}

impl DecimalError {
    #[doc(hidden)]
    pub fn _description(&self) -> &str {
        match self {
            DecimalError::PrecLimitExceeded => {
                "Result exceeds the precision limit."
            }
            DecimalError::InternalOverflow => {
                "Internal representation exceeded."
            }
            DecimalError::InfiniteValue => {
                "Can't convert infinite value to Decimal."
            }
            DecimalError::NotANumber => "Given value is not a number.",
            DecimalError::DivisionByZero => "Division by Zero.",
        }
    }
}

impl Display for DecimalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self._description(), f)
    }
}

impl std::error::Error for DecimalError {}
