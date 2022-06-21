// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::cmp::Ordering;

use fpdec_core::checked_mul_pow_ten;

use crate::Decimal;

/// Checked addition.
/// Computes `self + rhs`.
/// Returns `None` if the result can not be represented by the `Output` type.
pub trait CheckedAdd<Rhs = Self> {
    /// The resulting type after applying `checked_add`.
    type Output;
    /// Returns `Some(self + rhs)` or `None` if the result can not be
    /// represented by the `Output` type.
    fn checked_add(self, rhs: Rhs) -> Self::Output;
}

/// Checked subtraction.
/// Computes `self - rhs`.
/// Returns `None` if the result can not be represented by the `Output` type.
pub trait CheckedSub<Rhs = Self> {
    /// The resulting type after applying `checked_sub`.
    type Output;
    /// Returns `Some(self - rhs)` or `None` if the result can not be
    /// represented by the `Output` type.
    fn checked_sub(self, rhs: Rhs) -> Self::Output;
}

macro_rules! impl_checked_add_sub_decimal {
    (impl $imp:ident, $method:ident) => {
        impl $imp<Self> for Decimal {
            type Output = Option<Self>;

            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                match self.n_frac_digits.cmp(&rhs.n_frac_digits) {
                    Ordering::Equal => Some(Self {
                        coeff: i128::$method(self.coeff, rhs.coeff)?,
                        n_frac_digits: self.n_frac_digits,
                    }),
                    Ordering::Greater => Some(Self {
                        coeff: i128::$method(
                            self.coeff,
                            checked_mul_pow_ten(
                                rhs.coeff,
                                self.n_frac_digits - rhs.n_frac_digits,
                            )?,
                        )?,
                        n_frac_digits: self.n_frac_digits,
                    }),
                    Ordering::Less => Some(Self {
                        coeff: i128::$method(
                            checked_mul_pow_ten(
                                self.coeff,
                                rhs.n_frac_digits - self.n_frac_digits,
                            )?,
                            rhs.coeff,
                        )?,
                        n_frac_digits: rhs.n_frac_digits,
                    }),
                }
            }
        }

        forward_ref_binop!(impl $imp, $method);
    };
}

impl_checked_add_sub_decimal!(impl CheckedAdd, checked_add);

impl_checked_add_sub_decimal!(impl CheckedSub, checked_sub);

#[cfg(test)]
mod checked_add_sub_decimal_tests {
    use super::*;

    #[test]
    fn test_checked_add() {
        let x = Decimal::new_raw(1234567890, 3);
        let y = x.checked_add(x).unwrap();
        assert_eq!(y.coefficient(), 2 * x.coefficient());
        let z = x.checked_add(Decimal::NEG_ONE).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() - 1000);
        let x = Decimal::new_raw(1234567890, 5);
        let y = Decimal::new_raw(890, 1);
        let z = x.checked_add(y).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() + y.coefficient() * 10000);
        let z = y.checked_add(x).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() + y.coefficient() * 10000);
        let z = x.checked_add(Decimal::NEG_ONE).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() - 100000);
    }

    #[test]
    fn test_checked_add_pos_overflow() {
        let x = Decimal::new_raw(i128::MAX - 19999, 4);
        let y = x.checked_add(Decimal::TWO);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_add_neg_overflow() {
        let x = Decimal::new_raw(i128::MIN + 99, 2);
        let y = x.checked_add(Decimal::NEG_ONE);
        assert!(y.is_none());
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn test_checked_sub() {
        let x = Decimal::new_raw(1234567890, 3);
        let y = x.checked_sub(x).unwrap();
        assert_eq!(y.coefficient(), 0);
        let z = x.checked_sub(Decimal::NEG_ONE).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() + 1000);
        let x = Decimal::new_raw(1234567890, 2);
        let y = Decimal::new_raw(890, 1);
        let z = x.checked_sub(y).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() - y.coefficient() * 10);
        let z = y.checked_sub(x).unwrap();
        assert_eq!(z.coefficient(), y.coefficient() * 10 - x.coefficient());
        let z = x.checked_sub(Decimal::NEG_ONE).unwrap();
        assert_eq!(z.coefficient(), x.coefficient() + 100);
    }

    #[test]
    fn test_checked_sub_pos_overflow() {
        let x = Decimal::new_raw(i128::MIN + 10, 0);
        let y = Decimal::TEN.checked_sub(x);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_sub_neg_overflow() {
        let x = Decimal::new_raw(i128::MIN + 99999, 4);
        let y = x.checked_sub(Decimal::TEN);
        assert!(y.is_none());
    }

    #[test]
    fn test_checked_add_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x.checked_add(y).unwrap();
        assert_eq!(z.coefficient(), (&x).checked_add(y).unwrap().coefficient());
        assert_eq!(z.coefficient(), x.checked_add(&y).unwrap().coefficient());
        assert_eq!(
            z.coefficient(),
            (&x).checked_add(&y).unwrap().coefficient()
        );
    }

    #[test]
    fn test_checked_sub_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x.checked_sub(y).unwrap();
        assert_eq!(z.coefficient(), (&x).checked_sub(y).unwrap().coefficient());
        assert_eq!(z.coefficient(), x.checked_sub(&y).unwrap().coefficient());
        assert_eq!(
            z.coefficient(),
            (&x).checked_sub(&y).unwrap().coefficient()
        );
    }
}

macro_rules! impl_checked_add_sub_decimal_and_int {
    (impl $imp:ident, $method:ident) => {
        impl_checked_add_sub_decimal_and_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl $imp<$t> for Decimal {
            type Output = Option<Decimal>;

            #[inline]
            fn $method(self, rhs: $t) -> Self::Output {
                let coeff = if self.n_frac_digits == 0 {
                    i128::$method(self.coeff, i128::from(rhs))
                } else {
                    i128::$method(
                        self.coeff,
                        checked_mul_pow_ten(i128::from(rhs), self.n_frac_digits)?
                    )
                }?;
                Some(Decimal { coeff, n_frac_digits: self.n_frac_digits })
            }
        }

        impl $imp<Decimal> for $t {
            type Output = Option<Decimal>;

            #[inline]
            fn $method(self, rhs: Decimal) -> Self::Output {
                let coeff = if rhs.n_frac_digits == 0 {
                    i128::$method(i128::from(self), rhs.coeff)
                } else {
                    i128::$method(
                        checked_mul_pow_ten(i128::from(self), rhs.n_frac_digits)?,
                        rhs.coeff
                    )
                }?;
                Some(Decimal { coeff, n_frac_digits: rhs.n_frac_digits })
            }
        }
        )*
    }
}

impl_checked_add_sub_decimal_and_int!(impl CheckedAdd, checked_add);
forward_ref_binop_decimal_int!(impl CheckedAdd, checked_add);

impl_checked_add_sub_decimal_and_int!(impl CheckedSub, checked_sub);
forward_ref_binop_decimal_int!(impl CheckedSub, checked_sub);

#[cfg(test)]
mod checked_add_sub_integer_tests {
    use fpdec_core::ten_pow;

    use super::*;

    macro_rules! gen_checked_add_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i = <$t>::MAX;
                let r = d.checked_add(i).unwrap();
                assert_eq!(r.n_frac_digits, d.n_frac_digits);
                assert_eq!(
                    r.coefficient(),
                    i128::from(i) * ten_pow($p) + $coeff
                );
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_add(i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    d.checked_add(&i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_add(&i).unwrap().coefficient()
                );
                let z = CheckedAdd::checked_add(i, d).unwrap();
                assert_eq!(z.coefficient(), r.coefficient());
                assert_eq!(
                    z.coefficient(),
                    CheckedAdd::checked_add(&i, d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedAdd::checked_add(i, &d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedAdd::checked_add(&i, &d).unwrap().coefficient()
                );
                let d = Decimal::new_raw(i128::MAX, $p);
                let i: $t = 1;
                let z = d.checked_add(i);
                assert!(z.is_none());
            }
        };
    }

    gen_checked_add_integer_tests!(test_checked_add_u8, u8, 2, 1);
    gen_checked_add_integer_tests!(test_checked_add_i8, i8, 0, 123);
    gen_checked_add_integer_tests!(test_checked_add_u16, u16, 4, 11);
    gen_checked_add_integer_tests!(test_checked_add_i16, i16, 4, 1234567);
    gen_checked_add_integer_tests!(test_checked_add_u32, u32, 1, 0);
    gen_checked_add_integer_tests!(test_checked_add_i32, i32, 9, 1234);
    gen_checked_add_integer_tests!(test_checked_add_u64, u64, 3, 321);
    gen_checked_add_integer_tests!(
        test_checked_add_i64,
        i64,
        7,
        12345678901234567890
    );

    #[test]
    fn test_checked_add_i128() {
        let d = Decimal::new_raw(1, 2);
        let i = 12345_i128;
        let r = d.checked_add(i).unwrap();
        assert_eq!(r.coefficient(), i * 100 + 1);
        assert_eq!(r.coefficient(), (&d).checked_add(i).unwrap().coefficient());
        assert_eq!(r.coefficient(), d.checked_add(&i).unwrap().coefficient());
        assert_eq!(
            r.coefficient(),
            (&d).checked_add(&i).unwrap().coefficient()
        );
        let z = CheckedAdd::checked_add(i, d).unwrap();
        assert_eq!(z.coefficient(), r.coefficient());
        assert_eq!(
            z.coefficient(),
            CheckedAdd::checked_add(&i, d).unwrap().coefficient()
        );
        assert_eq!(
            z.coefficient(),
            CheckedAdd::checked_add(i, &d).unwrap().coefficient()
        );
        assert_eq!(
            z.coefficient(),
            CheckedAdd::checked_add(&i, &d).unwrap().coefficient()
        );
    }

    macro_rules! gen_checked_sub_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i = <$t>::MAX;
                let r = d.checked_sub(i).unwrap();
                assert_eq!(
                    r.coefficient(),
                    $coeff - i128::from(i) * ten_pow($p)
                );
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_sub(i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    d.checked_sub(&i).unwrap().coefficient()
                );
                assert_eq!(
                    r.coefficient(),
                    (&d).checked_sub(&i).unwrap().coefficient()
                );
                let z = CheckedSub::checked_sub(i, d).unwrap();
                assert_eq!(
                    z.coefficient(),
                    i128::from(i) * ten_pow($p) - $coeff
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedSub::checked_sub(&i, d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedSub::checked_sub(i, &d).unwrap().coefficient()
                );
                assert_eq!(
                    z.coefficient(),
                    CheckedSub::checked_sub(&i, &d).unwrap().coefficient()
                );
                let d = Decimal::new_raw(i128::MIN, $p);
                let i: $t = 1;
                let z = d.checked_sub(i);
                assert!(z.is_none());
            }
        };
    }

    gen_checked_sub_integer_tests!(test_checked_sub_u8, u8, 2, 1);
    gen_checked_sub_integer_tests!(test_checked_sub_i8, i8, 0, 123);
    gen_checked_sub_integer_tests!(test_checked_sub_u16, u16, 4, 11);
    gen_checked_sub_integer_tests!(test_checked_sub_i16, i16, 4, 1234567);
    gen_checked_sub_integer_tests!(test_checked_sub_u32, u32, 1, 0);
    gen_checked_sub_integer_tests!(test_checked_sub_i32, i32, 9, 1234);
    gen_checked_sub_integer_tests!(test_checked_sub_u64, u64, 3, 321);
    gen_checked_sub_integer_tests!(
        test_checked_sub_i64,
        i64,
        7,
        12345678901234567890
    );

    #[test]
    fn test_checked_sub_i128() {
        let d = Decimal::new_raw(501, 2);
        let i = 12345_i128;
        let r = d.checked_sub(i).unwrap();
        assert_eq!(r.coefficient(), -i * 100 + 501);
        assert_eq!(r.coefficient(), (&d).checked_sub(i).unwrap().coefficient());
        assert_eq!(r.coefficient(), d.checked_sub(&i).unwrap().coefficient());
        assert_eq!(
            r.coefficient(),
            (&d).checked_sub(&i).unwrap().coefficient()
        );
        let z = CheckedSub::checked_sub(i, d).unwrap();
        assert_eq!(z.coefficient(), i * 100 - 501);
        assert_eq!(
            z.coefficient(),
            CheckedSub::checked_sub(&i, d).unwrap().coefficient()
        );
        assert_eq!(
            z.coefficient(),
            CheckedSub::checked_sub(i, &d).unwrap().coefficient()
        );
        assert_eq!(
            z.coefficient(),
            CheckedSub::checked_sub(&i, &d).unwrap().coefficient()
        );
    }
}
