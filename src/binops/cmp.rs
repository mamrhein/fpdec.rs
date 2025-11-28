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

#[cfg(feature = "rkyv")]
use crate::ArchivedDecimal;
use crate::Decimal;

macro_rules! impl_partial_eq {
    ($t:ty, $target:ty) => {
        impl PartialEq<$t> for $target {
            fn eq(&self, other: &$t) -> bool {
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
    };
}

impl_partial_eq!(Decimal, Decimal);
#[cfg(feature = "rkyv")]
impl_partial_eq!(ArchivedDecimal, ArchivedDecimal);
#[cfg(feature = "rkyv")]
impl_partial_eq!(Decimal, ArchivedDecimal);

#[cfg(feature = "rkyv")]
impl PartialEq<ArchivedDecimal> for Decimal {
    fn eq(&self, other: &ArchivedDecimal) -> bool {
        other.eq(self)
    }
}

impl Eq for Decimal {}

#[cfg(feature = "rkyv")]
impl Eq for ArchivedDecimal {}

macro_rules! impl_partial_ord {
    ($t:ty, $target:ty) => {
        #[allow(clippy::non_canonical_partial_ord_impl)]
        // Safe in this case because impl of Ord::cmp uses calls partial_cmp
        impl PartialOrd<$t> for $target {
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
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
    };
}

impl_partial_ord!(Decimal, Decimal);
#[cfg(feature = "rkyv")]
impl_partial_ord!(ArchivedDecimal, ArchivedDecimal);
#[cfg(feature = "rkyv")]
impl_partial_ord!(Decimal, ArchivedDecimal);

#[cfg(feature = "rkyv")]
impl PartialOrd<ArchivedDecimal> for Decimal {
    fn partial_cmp(&self, other: &ArchivedDecimal) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl Ord for Decimal {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(feature = "rkyv")]
impl Ord for ArchivedDecimal {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

macro_rules! impl_basics {
    ($ty:ty) => {
        impl $ty {
            /// Returns true if self is equal to zero.
            #[must_use]
            #[inline(always)]
            pub const fn eq_zero(&self) -> bool {
                self.coeff == 0
            }

            /// Returns true if self is equal to one.
            #[must_use]
            #[inline(always)]
            pub const fn eq_one(&self) -> bool {
                self.coeff == ten_pow(self.n_frac_digits)
            }

            /// Returns true if self is less than zero.
            #[must_use]
            #[inline(always)]
            pub const fn is_negative(&self) -> bool {
                self.coeff < 0
            }

            /// Returns true if self is greater than zero.
            #[must_use]
            #[inline(always)]
            pub const fn is_positive(&self) -> bool {
                self.coeff > 0
            }
        }
    };
}

impl_basics!(Decimal);
#[cfg(feature = "rkyv")]
impl_basics!(ArchivedDecimal);

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
                match checked_mul_pow_ten(i128::from(*other),
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
                match checked_mul_pow_ten(i128::from(*other),
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
                match checked_mul_pow_ten(i128::from(*other),
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
                match checked_mul_pow_ten(i128::from(*self),
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
                match checked_mul_pow_ten(i128::from(*other),
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
                match checked_mul_pow_ten(i128::from(*self),
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

#[cfg(feature = "rkyv")]
#[cfg(test)]
mod rkyv_cmp_decimals_tests {
    use rkyv;

    use super::*;

    macro_rules! declare {
        ($i:ident = $x:expr, $a:ident) => {
            let $i = $x;
            let bytes = rkyv::to_bytes::<_, 256>(&$i).unwrap();
            let $a =
                rkyv::check_archived_root::<Decimal>(&bytes[..]).unwrap();
        };
    }

    #[test]
    fn test_eq_same_n_frac_digits() {
        declare!(x = Decimal::new_raw(178, 1), a);
        assert!(x.eq(a));
        assert!(!(a.ne(&x)));
    }

    #[test]
    fn test_eq_different_n_frac_digits() {
        declare!(x = Decimal::new_raw(178, 1), x_a);
        declare!(y = Decimal::new_raw(178000, 4), y_a);

        assert!(x.eq(y_a));
        assert!(x_a.eq(&y));

        assert_eq!(x, *y_a);
        assert_eq!(y, *x_a);
        assert_eq!(*x_a, y);
        assert_eq!(*y_a, x);

        assert!(!(y.ne(x_a)));
        assert!(!(y_a.ne(&x)));
    }

    #[test]
    fn test_ne_same_n_frac_digits() {
        declare!(x = Decimal::new_raw(-178000, 7), x_a);
        declare!(y = Decimal::new_raw(178000, 7), y_a);

        assert_ne!(x, *y_a);
        assert_ne!(*x_a, y);

        assert_eq!(x.partial_cmp(y_a), Some(Ordering::Less));
        assert_eq!(x_a.partial_cmp(&y), Some(Ordering::Less));

        assert_eq!(x_a.cmp(y_a), Ordering::Less);

        assert!(x < *y_a);
        assert!(*x_a < y);

        assert!(*y_a > x);
        assert!(y > *x_a);
    }

    #[test]
    fn test_ne_different_n_frac_digits() {
        declare!(x = Decimal::new_raw(178001, 7), x_a);
        declare!(y = Decimal::new_raw(178, 4), y_a);

        assert_ne!(x, *y_a);
        assert_ne!(*x_a, y);

        assert_eq!(x.partial_cmp(y_a), Some(Ordering::Greater));
        assert_eq!(x_a.partial_cmp(&y), Some(Ordering::Greater));

        assert!(x > *y_a);
        assert!(*x_a > y);

        assert!(*y_a < x);
        assert!(y < *x_a);
    }

    #[test]
    fn test_ne_lhs_adj_coeff_overflow() {
        let coeff = i128::MAX - 2;
        declare!(x = Decimal::new_raw(coeff, 4), x_a);
        declare!(y = Decimal::new_raw(coeff, 5), y_a);

        assert_ne!(x, *y_a);
        assert_ne!(*x_a, y);

        assert_eq!(x.partial_cmp(y_a), Some(Ordering::Greater));
        assert_eq!(x_a.partial_cmp(&y), Some(Ordering::Greater));

        assert!(x > *y_a);
        assert!(*x_a > y);

        assert!(*y_a < x);
        assert!(y < *x_a);
    }

    #[test]
    fn test_ne_rhs_adj_coeff_overflow() {
        let coeff = i128::MAX - 2;
        declare!(x = Decimal::new_raw(coeff, 4), x_a);
        declare!(y = Decimal::new_raw(coeff, 3), y_a);

        assert_ne!(x, *y_a);
        assert_ne!(*x_a, y);

        assert_eq!(x.partial_cmp(y_a), Some(Ordering::Less));
        assert_eq!(x_a.partial_cmp(&y), Some(Ordering::Less));

        assert!(x < *y_a);
        assert!(*x_a < y);

        assert!(*y_a > x);
        assert!(y > *x_a);
    }

    #[test]
    fn test_eq_zero() {
        declare!(zero1 = Decimal::ZERO, zero1_a);
        assert!(ArchivedDecimal::eq_zero(zero1_a));

        declare!(zero2 = Decimal::new_raw(0, 5), zero2_a);
        assert!(ArchivedDecimal::eq_zero(zero2_a));
    }

    #[test]
    fn test_eq_one() {
        declare!(one1 = Decimal::ONE, one1_a);
        assert!(ArchivedDecimal::eq_one(one1_a));

        declare!(one2 = Decimal::new_raw(10000, 4), one2_a);
        assert!(ArchivedDecimal::eq_one(one2_a));

        declare!(one3 = Decimal::new_raw(ten_pow(17), 17), one3_a);
        assert!(ArchivedDecimal::eq_one(one3_a));
    }
}
