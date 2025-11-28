// ---------------------------------------------------------------------------
// Copyright:   (c) 2023 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use fpdec_core::ten_pow;

use crate::{Decimal, TryFromDecimalError};

impl TryFrom<Decimal> for i128 {
    type Error = TryFromDecimalError;

    /// Tries to convert a `Decimal` value `d` into an `i128`.
    ///
    /// Returns the value as an `i128`, if it is representable as such,
    /// wrapped in Result::Ok.
    ///
    /// Returns an error (wrapped in Result::Err) in the following cases:
    /// * `d` is not an integral value =>
    ///   `TryFromDecimalError::NotAnIntValue`,
    /// * `d` exceeds the range of `ì128` values =>
    ///   `TryFromDecimalError::ValueOutOfRange`.
    #[allow(clippy::integer_division)]
    fn try_from(d: Decimal) -> Result<Self, Self::Error> {
        if d.n_frac_digits == 0 || d.coeff == 0 {
            Ok(d.coeff)
        } else {
            let t = ten_pow(d.n_frac_digits);
            if d.coeff % t == 0_i128 {
                Ok(d.coeff / t)
            } else {
                Err(TryFromDecimalError::NotAnIntValue)
            }
        }
    }
}

#[cfg(test)]
mod tests_into_i128 {
    use super::*;

    #[test]
    fn test_zero() {
        let t: i128 = Decimal::ZERO.try_into().unwrap();
        assert_eq!(t, 0_i128);
    }

    #[test]
    fn test_one() {
        let t = i128::try_from(Decimal::ONE);
        assert_eq!(t.unwrap(), 1_i128);
    }

    #[test]
    fn test_neg_one() {
        let t = i128::try_from(Decimal::NEG_ONE);
        assert_eq!(t.unwrap(), -1_i128);
    }

    #[test]
    fn test_max() {
        let t = TryInto::<i128>::try_into(Decimal::MAX);
        assert_eq!(t.unwrap(), i128::MAX);
    }

    #[test]
    fn test_delta() {
        let t = i128::try_from(Decimal::DELTA);
        assert!(t.is_err());
        assert_eq!(t.unwrap_err(), TryFromDecimalError::NotAnIntValue);
    }

    #[test]
    fn test_non_int() {
        let d = Decimal::new_raw(1, 1);
        let t = TryInto::<i128>::try_into(d);
        assert!(t.is_err());
        assert_eq!(t.unwrap_err(), TryFromDecimalError::NotAnIntValue);
    }
}

macro_rules! impl_int_from_dec {
    () => {
        impl_int_from_dec!(u8, i8, u16, i16, u32, i32, u64, i64, u128);
    };
    ($($t:ty),*) => {
        $(
        impl TryFrom<Decimal> for $t {
            type Error = TryFromDecimalError;

            #[doc="Tries to convert a `Decimal` value `d` into an `"]
            #[doc=stringify!($t)]
            #[doc="`.\n\nReturns the value as `"]
            #[doc=stringify!($t)]
            #[doc="`, if it is representable as such, wrapped in Result::Ok."]
            #[doc="\n\nReturns an error (wrapped in Result::Err) in the \
            following cases:"]
            #[doc=" * `d` is not an integral value => \
            `TryFromDecimalError::NotAnIntValue`,"]
            #[doc=" * `d` exceeds the range of `"]
            #[doc=stringify!($t)]
            #[doc="` values => `TryFromDecimalError::ValueOutOfRange`."]
            fn try_from(d: Decimal) -> Result<Self, Self::Error> {
                match i128::try_from(d) {
                    Ok(i) => {
                        match Self::try_from(i) {
                            Ok(i) => Ok(i),
                            Err(_) => Err(TryFromDecimalError::ValueOutOfRange),
                        }
                    },
                    Err(e) => Err(e),
                }
            }
        }
        )*
    }
}

impl_int_from_dec!();

#[cfg(test)]
mod tests_into_int {
    use super::*;

    #[test]
    fn test_zero() {
        let t = i8::try_from(Decimal::ZERO);
        assert_eq!(t.unwrap(), 0_i8);
    }

    #[test]
    fn test_one() {
        let t: i32 = Decimal::ONE.try_into().unwrap();
        assert_eq!(t, 1_i32);
    }

    #[test]
    fn test_neg_one() {
        let t = TryInto::<i64>::try_into(Decimal::NEG_ONE);
        assert_eq!(t.unwrap(), -1_i64);
        let t = TryInto::<u64>::try_into(Decimal::NEG_ONE);
        assert!(t.is_err());
        assert_eq!(t.unwrap_err(), TryFromDecimalError::ValueOutOfRange);
    }

    #[test]
    fn test_max() {
        let t = u128::try_from(Decimal::MAX);
        assert_eq!(t.unwrap(), i128::MAX as u128);
        let t = u64::try_from(Decimal::MAX);
        assert!(t.is_err());
        assert_eq!(t.unwrap_err(), TryFromDecimalError::ValueOutOfRange);
    }

    #[test]
    fn test_delta() {
        let t: Result<i16, TryFromDecimalError> = Decimal::DELTA.try_into();
        assert!(t.is_err());
        assert_eq!(t.unwrap_err(), TryFromDecimalError::NotAnIntValue);
    }

    #[test]
    fn test_non_int() {
        let d = Decimal::new_raw(1, 1);
        let t = u32::try_from(d);
        assert!(t.is_err());
        assert_eq!(t.unwrap_err(), TryFromDecimalError::NotAnIntValue);
    }

    #[test]
    fn test_truncated() {
        let d = Decimal::new_raw(12345, 3);
        let t: u8 = d.trunc().try_into().unwrap();
        assert_eq!(t, 12_u8);
    }
}
