// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::cmp::Ordering;

use fpdec_core::{checked_adjust_coeffs, checked_mul_pow_ten, ten_pow};

use crate::Decimal;

impl PartialEq<Decimal> for Decimal {
    fn eq(&self, other: &Decimal) -> bool {
        match checked_adjust_coeffs(
            self.coeff,
            self.n_frac_digits,
            other.coeff,
            other.n_frac_digits,
        ) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Decimal {}

impl PartialOrd<Decimal> for Decimal {
    fn partial_cmp(&self, other: &Decimal) -> Option<Ordering> {
        match checked_adjust_coeffs(
            self.coeff,
            self.n_frac_digits,
            other.coeff,
            other.n_frac_digits,
        ) {
            (Some(a), Some(b)) => a.partial_cmp(&b),
            (None, Some(_)) => {
                if self.coeff > 0 {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            (Some(_), None) => {
                if other.coeff < 0 {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            // Should never happen:
            (None, None) => None,
        }
    }
}

impl Ord for Decimal {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Decimal {
    /// Returns true if self is equal to zero.
    #[inline(always)]
    pub fn eq_zero(&self) -> bool {
        self.coeff == 0
    }

    /// Returns true if self is equal to one.
    #[inline(always)]
    pub fn eq_one(&self) -> bool {
        self.coeff == ten_pow(self.n_frac_digits)
    }

    /// Returns true if self is less than zero.
    #[inline(always)]
    pub fn is_negative(&self) -> bool {
        self.coeff < 0
    }

    /// Returns true if self is greater than zero.
    #[inline(always)]
    pub fn is_positive(&self) -> bool {
        self.coeff > 0
    }
}

#[cfg(test)]
mod cmp_decimals_tests {
    use core::cmp::{max, min};

    use fpdec_core::ten_pow;

    use super::*;

    #[test]
    fn test_eq_same_n_frac_digits() {
        let x = Decimal::new_raw(178, 1);
        assert!(x.eq(&x));
        let y = x;
        assert!(x.eq(&y));
        assert_eq!(x, y);
        assert_eq!(y, x);
        assert!(!(y.ne(&x)));
    }

    #[test]
    fn test_eq_different_n_frac_digits() {
        let x = Decimal::new_raw(178, 1);
        let y = Decimal::new_raw(178000, 4);
        assert!(x.eq(&y));
        assert_eq!(x, y);
        assert_eq!(y, x);
        assert!(!(y.ne(&x)));
    }

    #[test]
    fn test_ne_same_n_frac_digits() {
        let x = Decimal::new_raw(-178000, 7);
        let y = Decimal::new_raw(178000, 7);
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert_eq!(x.cmp(&y), Ordering::Less);
        assert!(x < y);
        assert!(y > x);
    }

    #[test]
    fn test_ne_different_n_frac_digits() {
        let x = Decimal::new_raw(178001, 7);
        let y = Decimal::new_raw(178, 4);
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Greater));
        assert!(x > y);
        assert!(y < x);
    }

    #[test]
    fn test_ne_lhs_adj_coeff_overflow() {
        let coeff = i128::MAX - 2;
        let x = Decimal::new_raw(coeff, 4);
        let y = Decimal::new_raw(coeff, 5);
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Greater));
        assert_eq!(x.cmp(&y), Ordering::Greater);
        assert!(x > y);
        assert!(y < x);
    }

    #[test]
    fn test_ne_rhs_adj_coeff_overflow() {
        let coeff = i128::MAX - 2;
        let x = Decimal::new_raw(coeff, 4);
        let y = Decimal::new_raw(coeff, 3);
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert_eq!(x.cmp(&y), Ordering::Less);
        assert!(x < y);
        assert!(y > x);
    }

    #[test]
    fn test_min_max() {
        let x = Decimal::new_raw(12345, 2);
        let y = Decimal::new_raw(12344, 2);
        assert_eq!(min(x, y), y);
        assert_eq!(min(x, x), x);
        assert_eq!(max(x, y), x);
        assert_eq!(max(x, x), x);
    }

    #[test]
    fn test_min_max_lhs_adj_coeff_overflow() {
        let coeff = i128::MAX - 7;
        let x = Decimal::new_raw(coeff, 1);
        let y = Decimal::new_raw(coeff, 2);
        assert_eq!(min(x, y), y);
        assert_eq!(max(x, y), x);
    }

    #[test]
    fn test_min_max_rhs_adj_coeff_overflow() {
        let coeff = i128::MIN + 7;
        let x = Decimal::new_raw(coeff, 1);
        let y = Decimal::new_raw(coeff, 0);
        assert_eq!(min(x, y), y);
        assert_eq!(max(x, y), x);
    }

    #[test]
    fn test_eq_zero() {
        assert!(Decimal::eq_zero(&Decimal::ZERO));
        assert!(Decimal::eq_zero(&Decimal::new_raw(0, 5)));
    }

    #[test]
    fn test_eq_one() {
        assert!(Decimal::eq_one(&Decimal::ONE));
        assert!(Decimal::eq_one(&Decimal::new_raw(10000, 4)));
        assert!(Decimal::eq_one(&Decimal::new_raw(ten_pow(17), 17)));
    }
}

macro_rules! impl_decimal_eq_uint {
    () => {
        impl_decimal_eq_uint!(u8, u16, u32, u64);
    };
    ($($t:ty),*) => {
        $(
        impl PartialEq<$t> for Decimal {
            #[inline]
            fn eq(&self, other: &$t) -> bool {
                if self.is_negative() {
                    return false;
                }
                match checked_mul_pow_ten((*other) as i128,
                                          self.n_frac_digits) {
                    Some(coeff) => self.coeff == coeff,
                    None => false,
                }
            }
        }
        )*
    }
}

impl_decimal_eq_uint!();

macro_rules! impl_decimal_eq_signed_int {
    () => {
        impl_decimal_eq_signed_int!(i8, i16, i32, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl PartialEq<$t> for Decimal {
            #[inline(always)]
            fn eq(&self, other: &$t) -> bool {
                match checked_mul_pow_ten((*other) as i128,
                                          self.n_frac_digits) {
                    Some(coeff) => self.coeff == coeff,
                    None => false,
                }
            }
        }
        )*
    }
}

impl_decimal_eq_signed_int!();

macro_rules! impl_int_eq_decimal {
    () => {
        impl_int_eq_decimal!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl PartialEq<Decimal> for $t
        where
            Decimal: PartialEq<$t>,
        {
            #[inline(always)]
            fn eq(&self, other: &Decimal) -> bool {
                PartialEq::eq(other, self)
            }
        }
        )*
    }
}

impl_int_eq_decimal!();

macro_rules! impl_decimal_cmp_signed_int {
    () => {
        impl_decimal_cmp_signed_int!(i8, i16, i32, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl PartialOrd<$t> for Decimal {
            #[inline]
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                match checked_mul_pow_ten((*other) as i128,
                                          self.n_frac_digits) {
                    Some(coeff) => self.coefficient().partial_cmp(&coeff),
                    None => {
                        if *other >= 0 {
                            Some(Ordering::Less)
                        } else {
                            Some(Ordering::Greater)
                        }
                    },
                }
            }
        }
        )*
    }
}

impl_decimal_cmp_signed_int!();

macro_rules! impl_signed_int_cmp_decimal {
    () => {
        impl_signed_int_cmp_decimal!(i8, i16, i32, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl PartialOrd<Decimal> for $t {
            #[inline]
            fn partial_cmp(&self, other: &Decimal) -> Option<Ordering> {
                match checked_mul_pow_ten((*self) as i128,
                                          other.n_frac_digits) {
                    Some(coeff) => coeff.partial_cmp(&other.coefficient()),
                    None => {
                        if *self < 0 {
                            Some(Ordering::Less)
                        } else {
                            Some(Ordering::Greater)
                        }
                    },
                }
            }
        }
        )*
    }
}

impl_signed_int_cmp_decimal!();

macro_rules! impl_decimal_cmp_uint {
    () => {
        impl_decimal_cmp_uint!(u8, u16, u32, u64);
    };
    ($($t:ty),*) => {
        $(
        impl PartialOrd<$t> for Decimal {
            #[inline]
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                if self.is_negative() {
                    return Some(Ordering::Less);
                }
                match checked_mul_pow_ten((*other) as i128,
                                           self.n_frac_digits) {
                    Some(coeff) => self.coefficient().partial_cmp(&coeff),
                    None => Some(Ordering::Less),
                }
            }
        }
        )*
    }
}

impl_decimal_cmp_uint!();

macro_rules! impl_uint_cmp_decimal {
    () => {
        impl_uint_cmp_decimal!(u8, u16, u32, u64);
    };
    ($($t:ty),*) => {
        $(
        impl PartialOrd<Decimal> for $t {
            #[inline]
            fn partial_cmp(&self, other: &Decimal) -> Option<Ordering> {
                if other.is_negative() {
                    return Some(Ordering::Greater);
                }
                match checked_mul_pow_ten((*self) as i128,
                                          other.n_frac_digits) {
                    Some(coeff) => coeff.partial_cmp(&other.coefficient()),
                    None => Some(Ordering::Greater),
                }
            }
        }
        )*
    }
}

impl_uint_cmp_decimal!();

#[cfg(test)]
mod cmp_decimals_and_ints_tests {
    use core::cmp::Ordering;

    use crate::Decimal;

    #[test]
    fn test_eq() {
        let x = Decimal::new_raw(170, 1);
        assert!(x.eq(&x));
        let y = 17_u8;
        assert!(x.eq(&y));
        assert!(y.eq(&x));
        let y = 17_u32;
        assert!(x.eq(&y));
        assert!(y.eq(&x));
        let y = 17_i128;
        assert_eq!(x, y);
        assert_eq!(y, x);
    }

    #[test]
    fn test_ne() {
        let x = Decimal::new_raw(-178, 7);
        let y = 0_i8;
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert!(x < y);
        assert!(y > x);
        let y = 1_u32;
        assert_ne!(x, y);
        assert_eq!(x.partial_cmp(&y), Some(Ordering::Less));
        assert!(x < y);
        assert!(y > x);
        let x = Decimal::new_raw(178, 1);
        let y = 18_u64;
        assert_ne!(x, y);
        assert!(x <= y);
        assert!(y >= x);
    }
}
