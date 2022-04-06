// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use crate::{binops::rem::rem, Decimal};

/// Checked remainder.
/// Computes `self % rhs`.
/// Returns `None` if the result can not be represented by the `Output` type.
pub trait CheckedRem<Rhs = Self> {
    /// The resulting type after applying `checked_rem`.
    type Output;
    /// Returns `Some(self % rhs)` or `None` if the result can not be
    /// represented by the `Output` type.
    fn checked_rem(self, rhs: Rhs) -> Self::Output;
}

impl CheckedRem<Decimal> for Decimal {
    type Output = Option<Decimal>;

    #[inline(always)]
    fn checked_rem(self, rhs: Decimal) -> Self::Output {
        if rhs.eq_zero() {
            return None;
        }
        if self.eq_zero() {
            return Some(Self::ZERO);
        }
        if rhs.eq_one() {
            return Some(self.fract());
        }
        match rem(self.coeff, self.n_frac_digits, rhs.coeff, rhs.n_frac_digits)
        {
            Ok((coeff, n_frac_digits)) => Some(Self {
                coeff,
                n_frac_digits,
            }),
            Err(_) => None,
        }
    }
}

forward_ref_binop!(impl CheckedRem, checked_rem);

#[cfg(test)]
mod checked_rem_decimal_tests {
    use super::*;

    #[test]
    fn test_checked_rem_same_prec() {
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(300, 2);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), 102);
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(-307, 2);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), 88);
        let x = Decimal::new_raw(-702, 2);
        let y = Decimal::new_raw(307, 2);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), -88);
        let x = Decimal::new_raw(702, 3);
        let y = Decimal::new_raw(300, 2);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), 702);
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(-307, 5);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), 198);
        let x = Decimal::new_raw(-702, 2);
        let y = Decimal::new_raw(307, 4);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), -204);
    }

    #[test]
    fn test_checked_rem_by_one() {
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::ONE;
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), x.fract().coefficient());
        let x = Decimal::new_raw(70389032, 4);
        let y = Decimal::new_raw(100, 2);
        let r = x.checked_rem(y).unwrap();
        assert_eq!(r.coefficient(), x.fract().coefficient());
    }

    #[test]
    fn test_checked_rem_ovfl() {
        let x = Decimal::new_raw(i128::MAX / 3, 1);
        let y = Decimal::new_raw(i128::MAX / 5, 3);
        let r = x.checked_rem(y);
        assert_eq!(r, None);
    }
}

macro_rules! impl_checked_rem_decimal_and_int {
    () => {
        impl_checked_rem_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl CheckedRem<$t> for Decimal {
            type Output = Option<Self>;

            fn checked_rem(self, rhs: $t) -> Self::Output {
                if rhs == 0 {
                    return None;
                }
                if self.eq_zero() {
                    return Some(Self::ZERO);
                }
                if rhs == 1 {
                    return Some(self.fract());
                }
                match rem(self.coeff, self.n_frac_digits, rhs as i128, 0) {
                    Ok((coeff, n_frac_digits)) => Some(Self {
                        coeff,
                        n_frac_digits,
                    }),
                    Err(_) => None,
                }
            }
        }

        impl CheckedRem<Decimal> for $t {
            type Output = Option<Decimal>;

            fn checked_rem(self, rhs: Decimal) -> Self::Output {
                if rhs.eq_zero() {
                    return None;
                }
                if self == 0 || rhs.eq_one() {
                    return Some(Decimal::ZERO);
                }
                match rem(self as i128, 0, rhs.coeff, rhs.n_frac_digits) {
                    Ok((coeff, n_frac_digits)) => Some(Decimal {
                        coeff,
                        n_frac_digits,
                    }),
                    Err(_) => None,
                }
            }
        }
        )*
    }
}

impl_checked_rem_decimal_and_int!();
forward_ref_binop_decimal_int!(impl CheckedRem, checked_rem);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod checked_rem_integer_tests {
    use fpdec_core::mul_pow_ten;

    use super::*;

    macro_rules! gen_checked_rem_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i: $t = 127;
                let c = mul_pow_ten(i as i128, $p);
                let r = d.checked_rem(i).unwrap();
                assert_eq!(r.coefficient(), $coeff - c * ($coeff / c));
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_rem(i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    d.checked_rem(&i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_rem(&i).unwrap().coefficient()
                );
                let z = CheckedRem::checked_rem(i, d).unwrap();
                assert_eq!(z.coefficient(), c - $coeff * (c / $coeff));
                assert_eq!(
                    z.coefficient(),
                    CheckedRem::checked_rem(&i, d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedRem::checked_rem(i, &d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedRem::checked_rem(&i, &d).unwrap().coefficient()
                );
            }
        };
    }

    gen_checked_rem_integer_tests!(test_checked_rem_u8, u8, 2, -1);
    gen_checked_rem_integer_tests!(test_checked_rem_i8, i8, 0, 253);
    gen_checked_rem_integer_tests!(test_checked_rem_u16, u16, 4, 804);
    gen_checked_rem_integer_tests!(test_checked_rem_i16, i16, 4, 390625);
    gen_checked_rem_integer_tests!(test_checked_rem_u32, u32, 1, 1014);
    gen_checked_rem_integer_tests!(test_checked_rem_i32, i32, 9, -1000);
    gen_checked_rem_integer_tests!(test_checked_rem_u64, u64, 3, 206);
    gen_checked_rem_integer_tests!(test_checked_rem_i64, i64, 7, -488281250);
    gen_checked_rem_integer_tests!(
        test_checked_rem_i128,
        i128,
        2,
        1526281250433765
    );

    #[test]
    fn test_checked_rem_decimal_by_int_one() {
        let x = Decimal::new_raw(17294738475, 5);
        let y = 1_i64;
        let z = x.checked_rem(y).unwrap();
        assert_eq!(z.coefficient(), x.fract().coefficient());
        let y = 1_u8;
        let z = x.checked_rem(y).unwrap();
        assert_eq!(z.coefficient(), x.fract().coefficient());
    }

    #[test]
    fn test_checked_rem_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::ONE;
        let z = CheckedRem::checked_rem(x, y).unwrap();
        assert_eq!(z.coefficient(), 0);
        let x = 1_u64;
        let y = Decimal::new_raw(1000000000000, 12);
        let z = CheckedRem::checked_rem(x, y).unwrap();
        assert_eq!(z.coefficient(), 0);
    }

    #[test]
    fn test_checked_rem_decimal_by_int_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = 0_i32;
        let z = x.checked_rem(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_rem_int_by_decimal_zero() {
        let x = 25_u64;
        let y = Decimal::new_raw(0, 3);
        let z = CheckedRem::checked_rem(x, y);
        assert!(z.is_none());
    }
}
