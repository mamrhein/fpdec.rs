// ----------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ----------------------------------------------------------------------------
// $Source$
// $Revision$

use core::convert::TryFrom;

use crate::{Decimal, DecimalError};

macro_rules! impl_from_int {
    () => {
        impl_from_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl From<$t> for Decimal {
            #[inline]
            fn from(i: $t) -> Self
            {
                Decimal { coeff: i as i128, n_frac_digits: 0 }
            }
        }
        )*
    }
}

impl_from_int!();

impl TryFrom<u128> for Decimal {
    type Error = DecimalError;

    #[inline]
    fn try_from(i: u128) -> Result<Self, Self::Error> {
        match i128::try_from(i) {
            Err(_) => Err(DecimalError::InternalOverflow),
            Ok(i) => Ok(Self::from(i)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_from_int<T>(numbers: &[T])
    where
        T: Into<i128> + Copy,
        Decimal: From<T>,
    {
        for n in numbers {
            let d = Decimal::from(*n);
            assert_eq!(d.coefficient(), (*n).into());
            assert_eq!(d.n_frac_digits(), 0);
        }
    }

    #[test]
    fn test_from_u8() {
        let numbers: [u8; 4] = [0, 1, 28, 255];
        check_from_int::<u8>(&numbers);
    }

    #[test]
    fn test_from_i8() {
        let numbers: [i8; 7] = [-128, -38, -1, 0, 1, 28, 127];
        check_from_int::<i8>(&numbers);
    }

    #[test]
    fn test_from_u64() {
        let numbers: [u64; 4] = [0, 1, 2128255, u64::MAX];
        check_from_int::<u64>(&numbers);
    }

    #[test]
    fn test_from_i64() {
        let numbers: [i64; 4] = [0, -1, 2128255, i64::MIN];
        check_from_int::<i64>(&numbers);
    }

    #[test]
    fn test_from_i128() {
        let numbers: [i128; 7] = [
            -170141183460469231731687303715884105728,
            -3830009274,
            -1,
            0,
            1,
            2829773566410082,
            170141183460469231731687303715884105727,
        ];
        check_from_int::<i128>(&numbers);
    }

    #[test]
    fn test_from_u128_ok() {
        let numbers: [u128; 4] =
            [0, 1, 2128255, 170141183460469231731687303715884105727u128];
        for n in numbers {
            match Decimal::try_from(n) {
                Err(_) => panic!("Misconfigured test case!"),
                Ok(d) => match i128::try_from(n) {
                    Err(_) => panic!("Should never happen!"),
                    Ok(i) => {
                        assert_eq!(d.coefficient(), i);
                        assert_eq!(d.n_frac_digits(), 0);
                    }
                },
            }
        }
    }

    #[test]
    fn test_from_u128_err() {
        let i = 170141183460469231731687303715884105728u128;
        let res = Decimal::try_from(i);
        assert_eq!(res.unwrap_err(), DecimalError::InternalOverflow);
    }

    #[test]
    fn test_from() {
        let si = -358_i32;
        let dsi = Decimal::from(si);
        assert_eq!(dsi.coefficient(), si as i128);
        assert_eq!(dsi.n_frac_digits(), 0);
        let ui = 38_u64.pow(12);
        let dui = Decimal::from(ui);
        assert_eq!(dui.coefficient(), ui as i128);
        assert_eq!(dui.n_frac_digits(), 0);
    }

    #[test]
    fn test_into() {
        let ui = 38_u8;
        let dui: Decimal = ui.into();
        assert_eq!(dui.coefficient(), ui as i128);
        assert_eq!(dui.n_frac_digits(), 0);
        let si = -1234567890123456789_i64;
        let dsi: Decimal = si.into();
        assert_eq!(dsi.coefficient(), si as i128);
        assert_eq!(dsi.n_frac_digits(), 0);
    }
}
