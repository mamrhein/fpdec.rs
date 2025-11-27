// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{
    cmp::Ordering,
    iter::Sum,
    ops::{Add, AddAssign, Sub, SubAssign},
};

use fpdec_core::mul_pow_ten;

use crate::Decimal;

macro_rules! impl_add_sub_decimal {
    (impl $imp:ident, $method:ident) => {
        impl $imp<Self> for Decimal {
            type Output = Self;

            #[inline]
            fn $method(self, rhs: Decimal) -> Self::Output {
                match self.n_frac_digits.cmp(&rhs.n_frac_digits) {
                    Ordering::Equal => Self::Output {
                        coeff: $imp::$method(self.coeff, rhs.coeff),
                        n_frac_digits: self.n_frac_digits,
                    },
                    Ordering::Greater => Self::Output {
                        coeff: $imp::$method(
                            self.coeff,
                            mul_pow_ten(
                                rhs.coeff,
                                self.n_frac_digits - rhs.n_frac_digits,
                            ),
                        ),
                        n_frac_digits: self.n_frac_digits,
                    },
                    Ordering::Less => Self::Output {
                        coeff: $imp::$method(
                            mul_pow_ten(
                                self.coeff,
                                rhs.n_frac_digits - self.n_frac_digits,
                            ),
                            rhs.coeff,
                        ),
                        n_frac_digits: rhs.n_frac_digits,
                    },
                }
            }
        }

        forward_ref_binop!(impl $imp, $method);
    };
}

impl_add_sub_decimal!(impl Add, add);

impl_add_sub_decimal!(impl Sub, sub);

#[cfg(test)]
mod add_sub_decimal_tests {
    use fpdec_core::ten_pow;

    use super::*;

    #[test]
    fn test_add_same_n_frac_digits() {
        let x = Decimal::new_raw(1234567890, 3);
        let y = x + x;
        assert_eq!(y.coefficient(), 2 * x.coefficient());
        assert_eq!(y.n_frac_digits(), x.n_frac_digits());
        let z = x + Decimal::NEG_ONE;
        assert_eq!(z.coefficient(), x.coefficient() - 1000);
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    fn test_add_different_n_frac_digits() {
        let x = Decimal::new_raw(1234567890, 5);
        let y = Decimal::new_raw(890, 1);
        let z = x + y;
        assert_eq!(
            z.coefficient(),
            x.coefficient() + y.coefficient() * 10000
        );
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
        let z = y + x;
        assert_eq!(
            z.coefficient(),
            x.coefficient() + y.coefficient() * 10000
        );
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
        let z = x + Decimal::NEG_ONE;
        assert_eq!(
            z.coefficient(),
            x.coefficient() - ten_pow(x.n_frac_digits())
        );
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    #[should_panic]
    fn test_add_pos_overflow() {
        let x = Decimal::new_raw(i128::MAX - 19999, 4);
        let _y = x + Decimal::TWO;
    }

    #[test]
    #[should_panic]
    fn test_add_neg_overflow() {
        let x = Decimal::new_raw(i128::MIN + 99, 2);
        let _y = x + Decimal::NEG_ONE;
    }

    #[test]
    #[allow(clippy::eq_op)]
    fn test_sub_same_n_frac_digits() {
        let x = Decimal::new_raw(1234567890, 3);
        let y = x - x;
        assert_eq!(y.coefficient(), 0);
        assert_eq!(y.n_frac_digits(), x.n_frac_digits());
        let z = x - Decimal::NEG_ONE;
        assert_eq!(
            z.coefficient(),
            x.coefficient() + ten_pow(x.n_frac_digits())
        );
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    fn test_sub_different_n_frac_digits() {
        let x = Decimal::new_raw(1234567890, 2);
        let y = Decimal::new_raw(890, 1);
        let z = x - y;
        assert_eq!(z.coefficient(), x.coefficient() - y.coefficient() * 10);
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
        let z = y - x;
        assert_eq!(z.coefficient(), y.coefficient() * 10 - x.coefficient());
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
        let z = x - Decimal::NEG_ONE;
        assert_eq!(
            z.coefficient(),
            x.coefficient() + ten_pow(x.n_frac_digits())
        );
        assert_eq!(z.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    #[should_panic]
    fn test_sub_pos_overflow() {
        let x = Decimal::new_raw(i128::MIN + 10, 0);
        let _y = Decimal::TEN - x;
    }

    #[test]
    #[should_panic]
    fn test_sub_neg_overflow() {
        let x = Decimal::new_raw(i128::MIN + 99999, 4);
        let _y = x - Decimal::TEN;
    }

    #[test]
    fn test_add_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x + y;
        assert_eq!(z.coefficient(), (&x + y).coefficient());
        assert_eq!(z.coefficient(), (x + &y).coefficient());
        assert_eq!(z.coefficient(), (&x + &y).coefficient());
    }

    #[test]
    fn test_sub_ref() {
        let x = Decimal::new_raw(12345, 3);
        let y = Decimal::new_raw(12345, 1);
        let z = x - y;
        assert_eq!(z.coefficient(), (&x - y).coefficient());
        assert_eq!(z.coefficient(), (x - &y).coefficient());
        assert_eq!(z.coefficient(), (&x - &y).coefficient());
    }
}

macro_rules! impl_add_sub_decimal_and_int {
    (impl $imp:ident, $method:ident) => {
        impl_add_sub_decimal_and_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl $imp<$t> for Decimal
        where
                {
            type Output = Decimal;

            #[inline(always)]
            fn $method(self, rhs: $t) -> Self::Output {
                if self.n_frac_digits == 0 {
                    Self::Output{
                        coeff: $imp::$method(self.coeff, i128::from(rhs)),
                        n_frac_digits: 0,
                    }
                } else {
                    Self::Output{
                        coeff: $imp::$method(self.coeff,
                                             mul_pow_ten(
                                                i128::from(rhs),
                                                self.n_frac_digits)),
                        n_frac_digits: self.n_frac_digits,
                    }
                }
            }
        }

        impl $imp<Decimal> for $t
        where
                {
            type Output = Decimal;

            #[inline(always)]
            fn $method(self, rhs: Decimal) -> Self::Output {
                if rhs.n_frac_digits == 0 {
                    Self::Output{
                        coeff: $imp::$method(i128::from(self), rhs.coeff),
                        n_frac_digits: 0,
                    }
                } else {
                    Self::Output{
                        coeff: $imp::$method(mul_pow_ten(
                                                i128::from(self),
                                                rhs.n_frac_digits),
                                             rhs.coeff),
                        n_frac_digits: rhs.n_frac_digits,
                    }
                }
            }
        }
        )*
    }
}

impl_add_sub_decimal_and_int!(impl Add, add);
forward_ref_binop_decimal_int!(impl Add, add);

impl_add_sub_decimal_and_int!(impl Sub, sub);
forward_ref_binop_decimal_int!(impl Sub, sub);

#[cfg(test)]
mod add_sub_integer_tests {
    use fpdec_core::ten_pow;

    use super::*;

    macro_rules! gen_add_integer_tests {
        ($func:ident, $t:ty, $n_frac_digits:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $n_frac_digits);
                let i = <$t>::MAX;
                let r = d + i;
                assert_eq!(r.n_frac_digits(), d.n_frac_digits());
                assert_eq!(
                    r.coefficient(),
                    i128::from(i) * ten_pow($n_frac_digits) + $coeff
                );
                assert_eq!(r.coefficient(), (&d + i).coefficient());
                assert_eq!(r.coefficient(), (d + &i).coefficient());
                assert_eq!(r.coefficient(), (&d + &i).coefficient());
                let z = i + d;
                assert_eq!(z.n_frac_digits(), r.n_frac_digits());
                assert_eq!(z.coefficient(), r.coefficient());
                assert_eq!(z.coefficient(), (&i + d).coefficient());
                assert_eq!(z.coefficient(), (i + &d).coefficient());
                assert_eq!(z.coefficient(), (&i + &d).coefficient());
            }
        };
    }

    gen_add_integer_tests!(test_add_u8, u8, 2, 1);
    gen_add_integer_tests!(test_add_i8, i8, 0, 123);
    gen_add_integer_tests!(test_add_u16, u16, 4, 11);
    gen_add_integer_tests!(test_add_i16, i16, 4, 1234567);
    gen_add_integer_tests!(test_add_u32, u32, 1, 0);
    gen_add_integer_tests!(test_add_i32, i32, 9, 1234);
    gen_add_integer_tests!(test_add_u64, u64, 3, 321);
    gen_add_integer_tests!(test_add_i64, i64, 7, 12345678901234567890);

    #[test]
    fn test_add_i128() {
        let d = Decimal::new_raw(1, 2);
        let i = 12345_i128;
        let r = d + i;
        assert_eq!(r.coefficient(), i * 100 + 1);
        assert_eq!(r.coefficient(), (&d + i).coefficient());
        assert_eq!(r.coefficient(), (d + &i).coefficient());
        assert_eq!(r.coefficient(), (&d + &i).coefficient());
        let z = i + d;
        assert_eq!(z.n_frac_digits(), r.n_frac_digits());
        assert_eq!(z.coefficient(), r.coefficient());
        assert_eq!(z.coefficient(), (&i + d).coefficient());
        assert_eq!(z.coefficient(), (i + &d).coefficient());
        assert_eq!(z.coefficient(), (&i + &d).coefficient());
    }

    macro_rules! gen_sub_integer_tests {
        ($func:ident, $t:ty, $n_frac_digits:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $n_frac_digits);
                let i = <$t>::MAX;
                let r = d - i;
                assert_eq!(r.n_frac_digits(), d.n_frac_digits());
                assert_eq!(
                    r.coefficient(),
                    $coeff - i128::from(i) * ten_pow($n_frac_digits)
                );
                assert_eq!(r.coefficient(), (&d - i).coefficient());
                assert_eq!(r.coefficient(), (d - &i).coefficient());
                assert_eq!(r.coefficient(), (&d - &i).coefficient());
                let z = i - d;
                assert_eq!(z.n_frac_digits(), r.n_frac_digits());
                assert_eq!(
                    z.coefficient(),
                    i128::from(i) * ten_pow($n_frac_digits) - $coeff
                );
                assert_eq!(z.coefficient(), (&i - d).coefficient());
                assert_eq!(z.coefficient(), (i - &d).coefficient());
                assert_eq!(z.coefficient(), (&i - &d).coefficient());
            }
        };
    }

    gen_sub_integer_tests!(test_sub_u8, u8, 2, 1);
    gen_sub_integer_tests!(test_sub_i8, i8, 0, 123);
    gen_sub_integer_tests!(test_sub_u16, u16, 4, 11);
    gen_sub_integer_tests!(test_sub_i16, i16, 4, 1234567);
    gen_sub_integer_tests!(test_sub_u32, u32, 1, 0);
    gen_sub_integer_tests!(test_sub_i32, i32, 9, 1234);
    gen_sub_integer_tests!(test_sub_u64, u64, 3, 321);
    gen_sub_integer_tests!(test_sub_i64, i64, 7, 12345678901234567890);

    #[test]
    fn test_sub_i128() {
        let d = Decimal::new_raw(501, 2);
        let i = 12345_i128;
        let r = d - i;
        assert_eq!(r.coefficient(), -i * 100 + 501);
        assert_eq!(r.coefficient(), (&d - i).coefficient());
        assert_eq!(r.coefficient(), (d - &i).coefficient());
        assert_eq!(r.coefficient(), (&d - &i).coefficient());
        let z = i - d;
        assert_eq!(z.coefficient(), i * 100 - 501);
        assert_eq!(z.coefficient(), (&i - d).coefficient());
        assert_eq!(z.coefficient(), (i - &d).coefficient());
        assert_eq!(z.coefficient(), (&i - &d).coefficient());
    }
}

forward_op_assign!(impl AddAssign, add_assign, Add, add);

forward_op_assign!(impl SubAssign, sub_assign, Sub, sub);

#[cfg(test)]
mod add_sub_assign_tests {
    use super::*;

    #[test]
    fn test_add_assign_decimal() {
        let mut x = Decimal::new_raw(1234567, 5);
        x += Decimal::new_raw(1, 4);
        assert_eq!(x.coefficient(), 1234577);
        x += Decimal::new_raw(88, 0);
        assert_eq!(x.coefficient(), 10034577);
    }

    #[test]
    fn test_add_assign_int() {
        let mut x = Decimal::new_raw(1234567, 5);
        x += 1_u32;
        assert_eq!(x.coefficient(), 1334567);
        x += -109_i8;
        assert_eq!(x.coefficient(), -9565433);
    }

    #[test]
    #[should_panic]
    fn test_add_assign_pos_overflow() {
        let mut x = Decimal::new_raw(i128::MAX - 19999, 4);
        x += Decimal::TWO;
    }

    #[test]
    #[should_panic]
    fn test_add_assign_neg_overflow() {
        let mut x = Decimal::new_raw(i128::MIN + 99, 2);
        x += Decimal::NEG_ONE;
    }

    #[test]
    fn test_sub_assign_decimal() {
        let mut x = Decimal::new_raw(1234567, 3);
        x -= Decimal::new_raw(100, 3);
        assert_eq!(x.coefficient(), 1234467);
        x -= Decimal::new_raw(1235, 0);
        assert_eq!(x.coefficient(), -533);
    }

    #[test]
    fn test_sub_assign_int() {
        let mut x = Decimal::new_raw(1234567, 2);
        x -= 1_u32;
        assert_eq!(x.coefficient(), 1234467_i128);
        x -= -109889_i128;
        assert_eq!(x.coefficient(), 12223367_i128);
    }

    #[test]
    #[should_panic]
    fn test_sub_assign_neg_overflow() {
        let mut x = Decimal::new_raw(i128::MIN + 99999, 4);
        x -= Decimal::TEN;
    }
}

impl Sum for Decimal {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |sum, next| sum + next)
    }
}

#[cfg(test)]
mod sum_tests {
    use fpdec_macros::Dec;

    use super::*;

    #[test]
    fn test_sum() {
        let sum = [Dec!(1.3), Dec!(2), Dec!(3), Dec!(4.1)]
            .into_iter()
            .sum::<Decimal>();

        assert_eq!(sum, Dec!(10.4));
    }
}
