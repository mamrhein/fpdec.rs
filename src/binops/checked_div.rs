// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use fpdec_core::MAX_N_FRAC_DIGITS;

use crate::{binops::div_rounded::checked_div_rounded, normalize, Decimal};

/// Checked division.
/// Computes `self / rhs`.
/// Returns `None` if the result can not be represented by the `Output` type.
pub trait CheckedDiv<Rhs = Self> {
    /// The resulting type after applying `checked_div`.
    type Output;
    /// Returns `Some(self / rhs)` or `None` if the result can not be
    /// represented by the `Output` type.
    fn checked_div(self, rhs: Rhs) -> Self::Output;
}

impl CheckedDiv<Self> for Decimal {
    type Output = Option<Self>;

    fn checked_div(self, rhs: Self) -> Self::Output {
        if rhs.eq_zero() {
            return None;
        }
        if self.eq_zero() {
            return Some(Self::ZERO);
        }
        if rhs.eq_one() {
            return Some(self);
        }
        let mut n_frac_digits = MAX_N_FRAC_DIGITS;
        let mut coeff = checked_div_rounded(
            self.coeff,
            self.n_frac_digits,
            rhs.coeff,
            rhs.n_frac_digits,
            n_frac_digits,
        )?;
        normalize(&mut coeff, &mut n_frac_digits);
        Some(Self {
            coeff,
            n_frac_digits,
        })
    }
}

forward_ref_binop!(impl CheckedDiv, checked_div);

#[cfg(test)]
mod checked_div_decimal_tests {
    use fpdec_core::mul_pow_ten;

    use super::*;

    #[test]
    fn test_checked_div() {
        let x = Decimal::new_raw(17, 0);
        let y = Decimal::new_raw(-200, 2);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), -85);
        assert_eq!(z.n_frac_digits(), 1);
        let x = Decimal::new_raw(17, 17);
        let y = Decimal::new_raw(2, 0);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), 85);
        assert_eq!(z.n_frac_digits(), 18);
        let x = Decimal::new_raw(12345678901234567890, 2);
        let y = Decimal::new_raw(244140625, 6);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), 5056790077945679007744);
        assert_eq!(z.n_frac_digits(), 7);
    }

    #[test]
    fn test_checked_div_frac_limit_exceeded() {
        let x = Decimal::new_raw(17, 1);
        let y = Decimal::new_raw(3, 0);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), 566666666666666667);
        assert_eq!(z.n_frac_digits(), 18);
    }

    #[test]
    fn test_checked_div_by_one() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ONE;
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), x.coefficient());
        let y = Decimal::new_raw(100000, 5);
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), x.coefficient());
    }

    #[test]
    fn test_checked_div_by_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = Decimal::ZERO;
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    // corner case where divident * shift overflows, but result doesn't
    #[test]
    fn test_checked_div_stepwise() {
        let x = Decimal::new_raw(mul_pow_ten(17, 17), 0);
        let y = Decimal::new_raw(20498, 5);
        let z = x.checked_div(y).unwrap();
        assert_eq!(
            z.coefficient(),
            8293492048004683383744755585910820568_i128
        );
        assert_eq!(z.n_frac_digits(), 18);
    }

    #[test]
    fn test_checked_div_overflow() {
        let x = Decimal::new_raw(mul_pow_ten(17, 20), 0);
        let y = Decimal::new_raw(2, 18);
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x.checked_div(y).unwrap();
        assert_eq!(
            z.coefficient(),
            (&x).checked_div(y).unwrap().coefficient()
        );
        assert_eq!(z.coefficient(), x.checked_div(&y).unwrap().coefficient());
        assert_eq!(
            z.coefficient(),
            (&x).checked_div(&y).unwrap().coefficient()
        );
    }
}

macro_rules! impl_div_decimal_and_int {
    () => {
        impl_div_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl CheckedDiv<$t> for Decimal {
            type Output = Option<Self>;

            fn checked_div(self, rhs: $t) -> Self::Output {
                if rhs == 0 {
                    return None;
                }
                if self.eq_zero() {
                    return Some(Self::ZERO);
                }
                if rhs == 1 {
                    return Some(self);
                }
                let mut n_frac_digits = MAX_N_FRAC_DIGITS;
                let mut coeff = checked_div_rounded(
                    self.coeff,
                    self.n_frac_digits,
                    i128::from(rhs),
                    0,
                    n_frac_digits,
                )?;
                normalize(&mut coeff, &mut n_frac_digits);
                Some(Self {
                    coeff,
                    n_frac_digits,
                })
            }
        }

        impl CheckedDiv<Decimal> for $t {
            type Output = Option<Decimal>;

            fn checked_div(self, rhs: Decimal) -> Self::Output {
                if rhs.eq_zero() {
                    return None;
                }
                if self == 0 {
                    return Some(Decimal::ZERO);
                }
                if rhs.eq_one() {
                    return Some(Decimal {
                        coeff: i128::from(self),
                        n_frac_digits: 0
                    });
                }
                let mut n_frac_digits = MAX_N_FRAC_DIGITS;
                let mut coeff = checked_div_rounded(
                    i128::from(self),
                    0,
                    rhs.coeff,
                    rhs.n_frac_digits,
                    n_frac_digits,
                )?;
                normalize(&mut coeff, &mut n_frac_digits);
                Some(Decimal {
                    coeff,
                    n_frac_digits,
                })
            }
        }
        )*
    }
}

impl_div_decimal_and_int!();
forward_ref_binop_decimal_int!(impl CheckedDiv, checked_div);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod checked_div_integer_tests {
    use fpdec_core::mul_pow_ten;

    use super::*;

    macro_rules! gen_checked_div_integer_tests {
        ($func:ident, $t:ty, $den:expr, $p:expr, $num:expr, $q:expr,
         $quot:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($num, $p);
                let i: $t = $den;
                let r = d.checked_div(i).unwrap();
                assert_eq!(r.coefficient(), $quot);
                assert_eq!(r.n_frac_digits(), $q);
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_div(i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    d.checked_div(&i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_div(&i).unwrap().coefficient()
                );
                let z = CheckedDiv::checked_div(i, d).unwrap();
                assert_eq!(z, CheckedDiv::checked_div(1_u8, r).unwrap());
                assert_eq!(
                    z.coefficient(),
                    CheckedDiv::checked_div(&i, d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedDiv::checked_div(i, &d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedDiv::checked_div(&i, &d).unwrap().coefficient()
                );
            }
        };
    }

    gen_checked_div_integer_tests!(test_checked_div_u8, u8, 5, 2, -1, 3, -2);
    gen_checked_div_integer_tests!(
        test_checked_div_i8,
        i8,
        115,
        0,
        230,
        0,
        2
    );
    gen_checked_div_integer_tests!(
        test_checked_div_u16,
        u16,
        160,
        4,
        80,
        5,
        5
    );
    gen_checked_div_integer_tests!(
        test_checked_div_i16,
        i16,
        25,
        4,
        390625,
        4,
        15625
    );
    gen_checked_div_integer_tests!(
        test_checked_div_u32,
        u32,
        40,
        1,
        10,
        3,
        25
    );
    gen_checked_div_integer_tests!(
        test_checked_div_i32,
        i32,
        -100,
        9,
        -1000,
        8,
        1
    );
    gen_checked_div_integer_tests!(
        test_checked_div_u64,
        u64,
        1250,
        4,
        31250,
        4,
        25
    );
    gen_checked_div_integer_tests!(
        test_checked_div_i64,
        i64,
        9765625,
        7,
        -488281250,
        6,
        -5
    );
    gen_checked_div_integer_tests!(
        test_checked_div_i128,
        i128,
        5005,
        0,
        2002,
        1,
        4
    );

    #[test]
    fn test_checked_div_decimal_by_int_one() {
        let x = Decimal::new_raw(17, 5);
        let y = 1_i64;
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), x.coefficient());
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
        let y = 1_u8;
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), x.coefficient());
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    fn test_checked_div_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::ONE;
        let z = CheckedDiv::checked_div(x, y).unwrap();
        assert_eq!(z.coefficient(), 17);
        assert_eq!(z.n_frac_digits(), 0);
        let x = 1_u64;
        let z = CheckedDiv::checked_div(x, y).unwrap();
        assert_eq!(z.coefficient(), 1);
        assert_eq!(z.n_frac_digits(), 0);
    }

    #[test]
    fn test_checked_div_int_by_decimal_frac_limit_exceeded() {
        let x = 3_i8;
        let y = Decimal::new_raw(17, 2);
        let z = CheckedDiv::checked_div(x, y).unwrap();
        assert_eq!(z.coefficient(), 17647058823529411765);
        assert_eq!(z.n_frac_digits(), 18);
    }

    #[test]
    fn test_checked_div_decimal_by_int_frac_limit_exceeded() {
        let x = Decimal::new_raw(17, 12);
        let y = 3_u8;
        let z = x.checked_div(y).unwrap();
        assert_eq!(z.coefficient(), 5666667);
        assert_eq!(z.n_frac_digits(), 18);
    }

    #[test]
    fn test_checked_div_decimal_by_int_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = 0_i32;
        let z = x.checked_div(y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_int_by_decimal_zero() {
        let x = 25_i64;
        let y = Decimal::ZERO;
        let z = CheckedDiv::checked_div(x, y);
        assert!(z.is_none());
    }

    #[test]
    fn test_checked_div_int_by_decimal_overflow() {
        let x = mul_pow_ten(17, 20);
        let y = Decimal::new_raw(2, 18);
        let z = CheckedDiv::checked_div(x, y);
        assert!(z.is_none());
    }
}
