// ---------------------------------------------------------------------------
// Copyright:   (c) 2023 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::mem::size_of;

use crate::Decimal;

#[inline(always)]
const fn n_signif_bits(v: u128) -> u32 {
    u128::BITS - v.leading_zeros()
}

trait Float: Sized {
    type B: Sized;
    #[allow(clippy::cast_possible_truncation)]
    const BITS: u32 = size_of::<Self::B>() as u32 * 8;
    const FRACTION_BITS: u32;
    const EXP_BIAS: i32;
    fn from_bits(bits: u64) -> Self;

    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_possible_wrap)]
    #[allow(clippy::cast_sign_loss)]
    #[allow(clippy::integer_division)]
    fn from_decimal(d: Decimal) -> Self {
        const EXTRA_BITS: u32 = 3;
        const MASK_EXTRA_BITS: [u128; 2] = [7, 3];
        const TIE: u32 = 4;

        let add_bits = Self::FRACTION_BITS + EXTRA_BITS;
        let mut num = d.coeff.unsigned_abs();
        let mut den = 10_u128.pow(d.n_frac_digits as u32);
        let num_lz = num.leading_zeros();
        let den_lz = den.leading_zeros();
        let num_shl = (num_lz + add_bits).saturating_sub(den_lz);
        let den_shl = den_lz.saturating_sub(num_lz).saturating_sub(add_bits);
        num <<= num_shl;
        den <<= den_shl;
        let quot = num / den;
        let rem = num % den;
        let adj = (n_signif_bits(quot) == add_bits) as usize;
        let mut rnd = ((quot & MASK_EXTRA_BITS[adj]) as u32) << adj as u32;
        rnd |= (rem != 0) as u32;
        let signif = (quot >> (EXTRA_BITS - adj as u32)) as u64;
        let exp = den_lz as i32 - num_lz as i32 - adj as i32;
        // signif has the hidden bit set, so we must subtract 1 from the
        // biased exponent!
        let mut bits = signif
            + (((Self::EXP_BIAS + exp - 1) as u64) << Self::FRACTION_BITS);
        bits += (rnd > TIE || rnd == TIE && (signif & 1) as u32 == 1) as u64;
        bits |= ((d.coeff < 0) as u64) << (Self::BITS - 1);
        Self::from_bits(bits)
    }
}

impl Float for f64 {
    type B = u64;
    const FRACTION_BITS: u32 = Self::MANTISSA_DIGITS - 1;
    const EXP_BIAS: i32 = Self::MAX_EXP - 1;

    #[inline(always)]
    fn from_bits(bits: u64) -> Self {
        Self::from_bits(bits)
    }
}

impl From<Decimal> for f64 {
    #[doc = "Converts a `Decimal` value `d` into an `f64`.\n"]
    #[doc = "Returns the value as `f64`, rounded to the nearest "]
    #[doc = "value representable as such."]
    #[inline(always)]
    #[allow(clippy::cast_precision_loss)]
    fn from(d: Decimal) -> Self {
        if d.n_frac_digits == 0 || d.coeff == 0 {
            d.coeff as Self
        } else {
            <Self as Float>::from_decimal(d)
        }
    }
}

#[cfg(test)]
mod tests_into_f64 {
    use super::*;

    #[test]
    fn test_zero() {
        let f = f64::from(Decimal::ZERO);
        assert_eq!(f, 0_f64);
    }

    #[test]
    fn test_neg_one() {
        let f = f64::from(Decimal::NEG_ONE);
        assert_eq!(f, -1_f64);
    }

    #[test]
    fn test_large_int_equiv() {
        let d = Decimal::new_raw(i128::MIN, 0);
        let f = f64::from(d);
        assert_eq!(f, -170141183460469231731687303715884105728_f64);
    }

    #[test]
    // Issue #13: 'subtract with overflow ' panic
    fn test_subtract_with_overflow_issue() {
        let d = Decimal::new_raw(10101010101010101, 18);
        let f = f64::from(d);
        assert_eq!(f, 0.010_101_010_101_010_1);
    }

    #[test]
    // Issue #14: Wrong rounding in conversion of Decimal to f64
    fn test_hard_to_round_1() {
        let d = Decimal::new_raw(9802266554071127_i128, 16);
        let f = f64::from(d);
        assert_eq!(f, 0.9802266554071127_f64);
    }

    #[test]
    // Issue #14: Wrong rounding in conversion of Decimal to f64
    fn test_hard_to_round_2() {
        let d = Decimal::new_raw(90071992547409905000000000001_i128, 13);
        let f = f64::from(d);
        assert_eq!(f, 9007199254740991_f64);
    }

    #[test]
    fn test_small_dec_1() {
        let d = Decimal::new_raw(12345678_i128, 3);
        let f = f64::from(d);
        assert_eq!(f, 12345.678_f64);
    }

    #[test]
    fn test_small_dec_2() {
        let d = Decimal::new_raw(0x001F_FFFF_FFFF_FFFF_i128, 7);
        let f = f64::from(d);
        assert_eq!(f, 900719925.4740991_f64);
    }

    #[test]
    fn test_large_dec_1() {
        let d = Decimal::new_raw(-0x007F_FFFF_FFFF_FFFF_i128, 2);
        let f = f64::from(d);
        assert_eq!(f, -360287970189639.7_f64);
    }

    #[test]
    fn test_large_dec_2() {
        let d = Decimal::new_raw(29007199254740997_i128, 1);
        let f = f64::from(d);
        assert_eq!(f, 2900719925474099.7_f64);
    }

    #[test]
    fn test_very_large_dec_1() {
        let d = Decimal::new_raw(-79614081257132168521894068557_i128, 12);
        let f = f64::from(d);
        assert_eq!(f, -79614081257132168.521894068557_f64);
    }

    #[test]
    fn test_very_large_dec_2() {
        let d = Decimal::new_raw(i128::MAX, 18);
        let f = f64::from(d);
        assert_eq!(f, 170141183460469231731.687303715884105727_f64);
    }
}

impl Float for f32 {
    type B = u32;
    const FRACTION_BITS: u32 = Self::MANTISSA_DIGITS - 1;
    const EXP_BIAS: i32 = Self::MAX_EXP - 1;

    #[inline(always)]
    #[allow(clippy::cast_possible_wrap)]
    #[allow(clippy::cast_possible_truncation)]
    fn from_bits(bits: u64) -> Self {
        Self::from_bits(bits as u32)
    }
}

impl From<Decimal> for f32 {
    #[doc = "Converts a `Decimal` value `d` into an `f32`.\n"]
    #[doc = "Returns the value as `f32`, rounded to the nearest "]
    #[doc = "value representable as such."]
    #[inline(always)]
    #[allow(clippy::cast_precision_loss)]
    fn from(d: Decimal) -> Self {
        if d.n_frac_digits == 0 || d.coeff == 0 {
            d.coeff as Self
        } else {
            <Self as Float>::from_decimal(d)
        }
    }
}

#[cfg(test)]
mod tests_into_f32 {
    use super::*;

    #[test]
    fn test_zero() {
        let f = f32::from(Decimal::ZERO);
        assert_eq!(f, 0_f32);
    }

    #[test]
    fn test_neg_one() {
        let f = f32::from(Decimal::NEG_ONE);
        assert_eq!(f, -1_f32);
    }

    #[test]
    fn test_large_int_equiv() {
        let d = Decimal::new_raw(i128::MIN, 0);
        let f = f32::from(d);
        assert_eq!(f, -170141183460469231731687303715884105728_f32);
    }

    #[test]
    fn test_small_dec_1() {
        let d = Decimal::new_raw(12345678_i128, 3);
        let f = f32::from(d);
        assert_eq!(f, 12345.678_f32);
    }

    #[test]
    fn test_small_dec_2() {
        let d = Decimal::new_raw(0x00FF_FFFD_i128, 7);
        let f = f32::from(d);
        assert_eq!(f, 1.6777213_f32);
    }

    #[test]
    fn test_large_dec_1() {
        let d = Decimal::new_raw(-134217933_i128, 2);
        let f = f32::from(d);
        assert_eq!(f, -1342179.4_f32);
    }

    #[test]
    fn test_large_dec_2() {
        let d = Decimal::new_raw(136739877_i128, 1);
        let f = f32::from(d);
        assert_eq!(f, 13673987.7_f32);
    }

    #[test]
    fn test_very_large_dec_1() {
        let d = Decimal::new_raw(-83734359738573_i128, 5);
        let f = f32::from(d);
        assert_eq!(f, -837343597.38573_f32);
    }

    #[test]
    fn test_very_large_dec_2() {
        let d = Decimal::new_raw(i128::MAX, 18);
        let f = f32::from(d);
        assert_eq!(f, 170141183460469231731.687303715884105727_f32);
    }
}
