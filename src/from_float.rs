// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::convert::TryFrom;

use fpdec_core::{div_mod_floor, magnitude, MAX_N_FRAC_DIGITS};

use crate::{normalize, Decimal, DecimalError};

// TODO: replace the following two functions when feature dec2flt got stable

/// Returns a normal f64 value f as (mantissa, exponent, sign) so that
/// `f = sign * mantissa * 2 ^ exponent`.
/// If f is signed zero or subnormal, (0, 0, 0) is returned.
fn f64_decode(f: f64) -> (u64, i16, i8) {
    let bits = f.to_bits();
    // sign bit at pos 63
    let sign_bit: u8 = (bits >> 63) as u8;
    // biased exponent at bit pos 52 .. 62
    let biased_exp = ((bits >> 52) & 0x7ff) as i16;
    // panic if f.is_infinite() or f.is_nan()
    assert_ne!(biased_exp, 0x7ff);
    // fraction at bit pos 0 .. 51
    let fraction = bits & 0xfffffffffffff;
    let (mantissa, exponent, sign) = if biased_exp == 0 {
        // f is signed zero or subnormal
        (0, 0, 0)
    } else {
        // f is normal
        (
            fraction | 0x10000000000000, // add integer bit
            biased_exp - 1023 - 52,      // exponent bias and fraction shift
            1 - (sign_bit << 1) as i8,   // map sign bit to sign (1 / -1)
        )
    };
    (mantissa, exponent, sign)
}

/// Returns a normal f32 value f as (mantissa, exponent, sign) so that
/// `f = sign * mantissa * 2 ^ exponent`.
/// If f is signed zero or subnormal, (0, 0, 0) is returned.
fn f32_decode(f: f32) -> (u64, i16, i8) {
    let bits = f.to_bits();
    // sign bit at pos 31
    let sign_bit: u8 = (bits >> 31) as u8;
    // biased exponent at bit pos 23 .. 30
    let biased_exp = ((bits >> 23) & 0xff) as i16;
    // panic if f.is_infinite() or f.is_nan()
    assert_ne!(biased_exp, 0xff);
    // fraction at bit pos 0 .. 22
    let fraction = (bits & 0x7fffff) as u64;
    let (mantissa, exponent, sign) = if biased_exp == 0 {
        // f is signed zero or subnormal
        (0, 0, 0)
    } else {
        // f is normal
        (
            fraction | 0x800000,       // add integer bit
            biased_exp - 127 - 23,     // exponent bias and fraction shift
            1 - (sign_bit << 1) as i8, // map sign bit to sign (1 / -1)
        )
    };
    (mantissa, exponent, sign)
}

const MAGN_I128_MAX: u8 = 38;

#[inline]
fn approx_rational(divident: i128, divisor: i128) -> (i128, u8) {
    assert!(divisor > 0);
    if divisor == 1 {
        return (divident, 0);
    }
    if divident == 0 {
        return (0, 0);
    }
    let mut n_frac_digits = 0_u8;
    let (mut coeff, mut rem) = div_mod_floor(divident, divisor);
    let mut magn_coeff = magnitude(coeff);
    while rem != 0
        && n_frac_digits < MAX_N_FRAC_DIGITS
        && magn_coeff < MAGN_I128_MAX - 1
    {
        // 0 < rem < divisor
        rem *= 10;
        // 0 < rem < 10 * divisor
        let quot = rem / divisor;
        // 0 <= quot < 10
        rem %= divisor;
        n_frac_digits += 1;
        magn_coeff += 1;
        coeff = coeff * 10 + quot;
    }
    // round coeff (half to even):
    // remainder > divisor / 2 or
    // remainder = divisor / 2 and quotient < 0
    // => add 1
    // here: 0 <= rem < divisor and divisor >= 2 => rem <= |divident| / 2,
    // therefor it's safe to use rem << 1
    rem <<= 1;
    if rem > divisor || rem == divisor && coeff < 0 {
        coeff += 1;
    }
    normalize(&mut coeff, &mut n_frac_digits);
    (coeff, n_frac_digits)
}

impl TryFrom<f32> for Decimal {
    type Error = DecimalError;

    //noinspection DuplicatedCode
    /// Tries to convert a `f32` value `f` into a `Decimal`.
    ///
    /// Returns the value representable as a `Decimal` which is nearest to `f`,
    /// if such a value exists, wrapped in Result::Ok.
    ///
    /// Returns an error (wrapped in Result::Err) in the following cases:
    /// * `f` is infinite => `DecimalError::InfiniteValue`,
    /// * `f` is Nan => `DecimalError::NotANumber`,
    /// * `f` > Decimal::MAX => `DecimalError::InternalOverflow`.
    ///
    /// Examples:
    ///
    /// ```rust
    /// # use fpdec::{Decimal, DecimalError};
    /// # use core::convert::TryFrom;
    /// # fn main() -> Result<(), DecimalError> {
    /// let d = Decimal::try_from(-289.5_f32)?;
    /// assert_eq!(d.to_string(), "-289.5");
    /// let d = Decimal::try_from(37.0005003_f32)?;
    /// assert_eq!(d.to_string(), "37.000499725341796875");
    /// # Ok(()) }
    /// ```
    fn try_from(f: f32) -> Result<Self, Self::Error> {
        if f.is_infinite() {
            return Err(DecimalError::InfiniteValue);
        }
        if f.is_nan() {
            return Err(DecimalError::NotANumber);
        }
        let (mantissa, exponent, sign) = f32_decode(f);
        if exponent < -126 {
            Ok(Decimal::ZERO)
        } else if exponent < 0 {
            let numer = i128::from(sign) * i128::from(mantissa);
            let denom = 1_i128 << ((-exponent) as usize);
            let (coeff, n_frac_digits) = approx_rational(numer, denom);
            Ok(Decimal {
                coeff,
                n_frac_digits,
            })
        } else {
            let numer = i128::from(sign) * i128::from(mantissa);
            let shift = 1_i128 << exponent as usize;
            match numer.checked_mul(shift) {
                Some(coeff) => Ok(Decimal {
                    coeff,
                    n_frac_digits: 0,
                }),
                None => Err(DecimalError::InternalOverflow),
            }
        }
    }
}

impl TryFrom<f64> for Decimal {
    type Error = DecimalError;

    //noinspection DuplicatedCode
    /// Tries to convert a `f64` value `f` into a `Decimal`.
    ///
    /// Returns the value representable as a `Decimal` which is nearest to `f`,
    /// if such a value exists, wrapped in Result::Ok.
    ///
    /// Returns an error (wrapped in Result::Err) in the following cases:
    /// * `f` is infinite => `DecimalError::InfiniteValue`,
    /// * `f` is Nan => `DecimalError::NotANumber`,
    /// * `f` > Decimal::MAX => `DecimalError::InternalOverflow`.
    ///
    /// Examples:
    ///
    /// ```rust
    /// # use fpdec::{Decimal, DecimalError};
    /// # use core::convert::TryFrom;
    /// # fn main() -> Result<(), DecimalError> {
    /// let d = Decimal::try_from(-289.5_f64)?;
    /// assert_eq!(d.to_string(), "-289.5");
    /// let d = Decimal::try_from(37.0005003_f64)?;
    /// assert_eq!(d.to_string(), "37.000500299999998788");
    /// # Ok(()) }
    /// ```
    fn try_from(f: f64) -> Result<Self, Self::Error> {
        if f.is_infinite() {
            return Err(DecimalError::InfiniteValue);
        }
        if f.is_nan() {
            return Err(DecimalError::NotANumber);
        }
        let (mantissa, exponent, sign) = f64_decode(f);
        if exponent < -126 {
            Ok(Decimal::ZERO)
        } else if exponent < 0 {
            let numer = i128::from(sign) * i128::from(mantissa);
            let denom = 1_i128 << ((-exponent) as usize);
            let (coeff, n_frac_digits) = approx_rational(numer, denom);
            Ok(Decimal {
                coeff,
                n_frac_digits,
            })
        } else {
            let numer = i128::from(sign) * i128::from(mantissa);
            let shift = 1_i128 << exponent as usize;
            match numer.checked_mul(shift) {
                Some(coeff) => Ok(Decimal {
                    coeff,
                    n_frac_digits: 0,
                }),
                None => Err(DecimalError::InternalOverflow),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_from_float<T>(test_data: &[(T, i128, u8)])
    where
        T: Copy,
        Decimal: TryFrom<T>,
    {
        for (val, coeff, n_frac_digits) in test_data {
            match Decimal::try_from(*val) {
                Err(_) => panic!("Mismatched test data: {}", coeff),
                Ok(d) => {
                    assert_eq!(d.coefficient(), *coeff);
                    assert_eq!(d.n_frac_digits(), *n_frac_digits);
                }
            }
        }
    }

    #[test]
    fn test_decimal0_from_f32() {
        let test_data = [
            (i128::MIN as f32, i128::MIN, 0),
            (-289.00, -289, 0),
            (-2., -2, 0),
            (0.0, 0, 0),
            (5., 5, 0),
            ((i128::MAX / 2) as f32, i128::MAX / 2 + 1, 0),
        ];
        check_from_float::<f32>(&test_data);
    }

    #[test]
    fn test_decimal_from_f32() {
        let test_data = [
            (-289.5_f32, -2895, 1),
            (-0.5005_f32, -500500023365020752, 18),
            (37.000503_f32, 370005035400390625, 16),
        ];
        check_from_float::<f32>(&test_data);
    }

    #[test]
    fn test_decimal0_from_f64() {
        let test_data = [
            (i128::MIN as f64, i128::MIN, 0),
            (-289.0, -289, 0),
            (-2., -2, 0),
            (0.0, 0, 0),
            (5.000, 5, 0),
            ((i128::MAX / 2) as f64, i128::MAX / 2 + 1, 0),
        ];
        check_from_float::<f64>(&test_data);
    }

    #[test]
    fn test_decimal_from_f64() {
        let test_data = [
            (-28900.000000005_f64, -28900000000004998582881, 18),
            (-5e-7, -5, 7),
            (1.004e-127, 0, 0),
            (1.0005, 1000499999999999945, 18),
            (37.0005000033, 37000500003299997331, 18),
        ];
        check_from_float::<f64>(&test_data);
    }

    #[test]
    fn test_fail_overflow() {
        let f = 5.839e38_f64;
        let res = Decimal::try_from(f);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::InternalOverflow);
    }

    #[test]
    fn test_fail_on_f32_infinite_value() {
        for f in [f32::INFINITY, f32::NEG_INFINITY] {
            let res = Decimal::try_from(f);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, DecimalError::InfiniteValue);
        }
    }

    #[test]
    fn test_fail_on_f64_infinite_value() {
        for f in [f64::INFINITY, f64::NEG_INFINITY] {
            let res = Decimal::try_from(f);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, DecimalError::InfiniteValue);
        }
    }

    #[test]
    fn test_fail_on_f32_nan() {
        let f = f32::NAN;
        let res = Decimal::try_from(f);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::NotANumber);
    }

    #[test]
    fn test_fail_on_f64_nan() {
        let f = f64::NAN;
        let res = Decimal::try_from(f);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, DecimalError::NotANumber);
    }
}
