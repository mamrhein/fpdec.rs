// ---------------------------------------------------------------------------
// Copyright:   (c) 2023 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use crate::{AsIntegerRatio, Decimal};

/// Return the number of significant bits in given i128.
#[inline(always)]
fn n_signif_bits(i: i128) -> u32 {
    debug_assert_ne!(i, 0);
    let u = i.abs();
    u128::BITS - u.leading_zeros() - u.trailing_zeros()
}

macro_rules! impl_into_float {
    () => {
        impl_into_float!(f32, f64);
    };
    ($($t:ty),*) => {
        $(
        impl From<Decimal> for $t {
            #[doc="Converts a `Decimal` value `d` into an `"]
            #[doc=stringify!($t)]
            #[doc="`.\n\nReturns the value as `"]
            #[doc=stringify!($t)]
            #[doc="`, rounded to the nearest value representable as such."]
            fn from(d: Decimal) -> Self {
                if d.n_frac_digits == 0 || d.coeff == 0 {
                    d.coeff as $t
                } else {
                    let (num, den) = d.as_integer_ratio();
                    if n_signif_bits(num) <= <$t>::MANTISSA_DIGITS {
                        // num is exactly representable as <T>
                        num as $t / den as $t
                    } else {
                        let q = num / den;
                        let r = num % den;
                        let nsb = n_signif_bits(q);
                        if nsb <= <$t>::MANTISSA_DIGITS {
                            // q is exactly representable as <T>
                            (q as $t) + (r as $t) / (den as $t)
                        } else {
                            // |q| >= 2^MANTISSA_DIGITS
                            let mut signif = q.abs() as u128;
                            let shr =
                                signif.trailing_zeros()
                                + nsb
                                - <$t>::MANTISSA_DIGITS;
                            debug_assert!(shr > 0);
                            let mut rem = (r != 0_i128) as u32;
                            rem |= match shr {
                                1 => ((signif as u32 & 1) << 2),
                                2 => ((signif as u32 & 3) << 1),
                                _ => ((signif & ((1_u128 << shr) - 1))
                                                    >> (shr - 3)) as u32,
                            };
                            signif >>= shr;
                            debug_assert_eq!(
                                u128::BITS - signif.leading_zeros(),
                                <$t>::MANTISSA_DIGITS
                            );
                            if rem > 4 ||
                                    rem == 4 && (signif as u32 & 1) == 1 {
                                signif += 1
                            }
                            let f = signif as $t * (shr as $t).exp2();
                            if q.is_positive() { f } else { -f }
                        }
                    }
                }
            }
        }
        )*
    }
}

impl_into_float!();

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
        assert_eq!(f, 0.010101010101010101);
    }

    #[test]
    fn test_small_dec_1() {
        let d = Decimal::new_raw(12345678_i128, 3);
        let f = f64::from(d);
        assert_eq!(f, 12345.678_f64);
    }

    #[test]
    fn test_small_dec_2() {
        let d = Decimal::new_raw(9007199254740991_i128, 7);
        let f = f64::from(d);
        assert_eq!(f, 900719925.4740991_f64);
    }

    #[test]
    fn test_large_dec_1() {
        let d = Decimal::new_raw(-36028797018963967_i128, 2);
        let f = f64::from(d);
        assert_eq!(f, -360287970189639.67_f64);
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
        let d = Decimal::new_raw(16777213_i128, 7);
        let f = f32::from(d);
        assert_eq!(f, 1.6777213_f32);
    }

    #[test]
    fn test_large_dec_1() {
        let d = Decimal::new_raw(-134217933_i128, 2);
        let f = f32::from(d);
        assert_eq!(f, -1342179.33_f32);
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
