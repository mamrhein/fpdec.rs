// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{ops::Add, str::FromStr};

use num_traits::{Num, One, Signed, Zero};

use crate::{Decimal, ParseDecimalError};

impl Zero for Decimal
where
    Self: Add<Output = Self>,
{
    #[inline(always)]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.eq_zero()
    }
}

#[cfg(test)]
mod zero_tests {
    use super::*;

    #[test]
    fn test_zero() {
        assert!(Decimal::is_zero(&Decimal::zero()));
        assert!(Decimal::is_zero(&Decimal::new_raw(0, 7)));
        assert!(!Decimal::is_zero(&Decimal::new_raw(1, 2)));
    }
}

impl One for Decimal {
    /// Returns the multiplicative identity element of Self, Self::ONE.
    #[inline(always)]
    fn one() -> Self {
        Self::ONE
    }

    /// Returns true if self is equal to the multiplicative identity.
    #[inline(always)]
    fn is_one(&self) -> bool {
        self.eq_one()
    }
}

#[cfg(test)]
mod one_tests {
    use super::*;

    #[test]
    fn test_one() {
        assert!(Decimal::is_one(&Decimal::one()));
        assert!(Decimal::is_one(&Decimal::new_raw(1000, 3)));
        assert!(!Decimal::is_one(&Decimal::new_raw(1, 1)));
    }
}

impl Num for Decimal {
    type FromStrRadixErr = <Self as FromStr>::Err;

    fn from_str_radix(
        str: &str,
        radix: u32,
    ) -> Result<Self, Self::FromStrRadixErr> {
        if radix != 10 {
            return Err(ParseDecimalError::Invalid);
        }
        Self::from_str(str)
    }
}

#[cfg(test)]
mod from_str_radix_tests {
    use super::*;

    #[test]
    fn test_from_str_radix() {
        let d = Decimal::from_str_radix("-17.5", 10).unwrap();
        assert_eq!(d.coefficient(), -175);
        assert_eq!(d.n_frac_digits(), 1);
    }

    #[test]
    fn test_err_invalid_radix() {
        let res = Decimal::from_str_radix("5.4", 16);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::Invalid);
    }
}

impl Signed for Decimal {
    /// Returns the absolute value of the number.
    #[inline(always)]
    fn abs(&self) -> Self {
        self.abs()
    }

    /// The positive difference of two numbers.
    ///
    /// Returns `zero` if the number is less than or equal to `other`,
    /// otherwise the difference between `self` and `other` is returned.
    fn abs_sub(&self, other: &Self) -> Self {
        if self <= other {
            Self::ZERO
        } else {
            self - other
        }
    }

    /// Returns the sign of the number.
    ///
    /// * `0` if the number is zero
    /// * `1` if the number is positive
    /// * `-1` if the number is negative
    #[inline(always)]
    fn signum(&self) -> Self {
        Self::from(self.coeff.signum())
    }

    /// Returns true if the number is positive and false if the number is zero
    /// or negative.
    #[inline(always)]
    fn is_positive(&self) -> bool {
        self.is_positive()
    }

    /// Returns true if the number is negative and false if the number is zero
    /// or positive.
    #[inline(always)]
    fn is_negative(&self) -> bool {
        self.is_negative()
    }
}

#[cfg(test)]
mod signed_tests {
    use super::*;

    #[test]
    fn test_abs_sub() {
        let x = Decimal::new_raw(12345_i128, 2);
        let y = Decimal::new_raw(12345_i128, 3);
        assert_eq!(x.abs_sub(&y), x - y);
        assert_eq!(y.abs_sub(&x), Decimal::ZERO);
    }
}
