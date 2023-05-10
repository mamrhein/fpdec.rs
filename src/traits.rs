// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{ops::Add, str::FromStr};

use num_traits::{Num, One, Zero};

use crate::{Decimal, ParseDecimalError};

impl Zero for Decimal
where
    Decimal: Add<Output = Decimal>,
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
    type FromStrRadixErr = <Decimal as FromStr>::Err;

    fn from_str_radix(
        str: &str,
        radix: u32,
    ) -> Result<Self, Self::FromStrRadixErr> {
        if radix != 10 {
            return Err(ParseDecimalError::Invalid);
        }
        Decimal::from_str(str)
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
