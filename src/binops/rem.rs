// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::{
    cmp::Ordering,
    ops::{Rem, RemAssign},
};

use fpdec_core::mul_pow_ten;

use crate::{Decimal, DecimalError};

impl Rem<Decimal> for Decimal {
    type Output = Decimal;

    #[inline(always)]
    fn rem(self, other: Decimal) -> Self::Output {
        if other.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        match self.n_frac_digits.cmp(&other.n_frac_digits) {
            Ordering::Equal => Self::Output {
                coeff: self.coeff % other.coeff,
                n_frac_digits: self.n_frac_digits,
            },
            Ordering::Greater => Self::Output {
                coeff: self.coeff
                    % mul_pow_ten(
                        other.coeff,
                        self.n_frac_digits - other.n_frac_digits,
                    ),
                n_frac_digits: self.n_frac_digits,
            },
            Ordering::Less => Self::Output {
                coeff: mul_pow_ten(
                    self.coeff,
                    other.n_frac_digits - self.n_frac_digits,
                ) % other.coeff,
                n_frac_digits: other.n_frac_digits,
            },
        }
    }
}

forward_ref_binop!(impl Rem, rem);

#[cfg(test)]
mod rem_decimal_tests {
    use super::*;

    #[test]
    fn test_rem_same_prec() {
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(300, 2);
        let r = x % y;
        assert_eq!(r.coeff, 102);
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(-307, 2);
        let r = x % y;
        assert_eq!(r.coeff, 88);
        let x = Decimal::new_raw(-702, 2);
        let y = Decimal::new_raw(307, 2);
        let r = x % y;
        assert_eq!(r.coeff, -88);
    }

    #[test]
    fn test_rem_diff_prec() {
        let x = Decimal::new_raw(702, 3);
        let y = Decimal::new_raw(300, 2);
        let r = x % y;
        assert_eq!(r.coeff, 702);
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(-307, 5);
        let r = x % y;
        assert_eq!(r.coeff, 198);
        let x = Decimal::new_raw(-702, 2);
        let y = Decimal::new_raw(307, 4);
        let r = x % y;
        assert_eq!(r.coeff, -204);
    }

    #[test]
    fn test_rem_by_one() {
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::ONE;
        let r = x % y;
        assert_eq!(r.coeff, x.fract().coeff);
        let x = Decimal::new_raw(70389032, 4);
        let y = Decimal::new_raw(100000, 5);
        let r = x % y;
        assert_eq!(r.coeff, x.fract().coeff * 10);
    }
}

macro_rules! impl_rem_decimal_and_int {
    () => {
        impl_rem_decimal_and_int!(u8, i8, u16, i16, u32, i32, u64, i64, i128);
    };
    ($($t:ty),*) => {
        $(
        impl Rem<$t> for Decimal {
            type Output = Decimal;

            fn rem(self, other: $t) -> Self::Output {
                if other == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self.n_frac_digits == 0 {
                    Self::Output {
                        coeff: self.coeff % other as i128,
                        n_frac_digits: 0,
                    }
                } else {
                    Self::Output {
                        coeff: self.coeff
                            % mul_pow_ten(other as i128, self.n_frac_digits),
                        n_frac_digits: self.n_frac_digits,
                    }
                }
            }
        }

        impl Rem<Decimal> for $t {
            type Output = Decimal;

            fn rem(self, other: Decimal) -> Self::Output {
                if other.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if other.n_frac_digits == 0 {
                    Self::Output {
                        coeff: self as i128 % other.coeff,
                        n_frac_digits: 0,
                    }
                } else {
                    Self::Output {
                        coeff: mul_pow_ten(self as i128, other.n_frac_digits)
                            % other.coeff,
                        n_frac_digits: other.n_frac_digits,
                    }
                }
            }
        }
        )*
    }
}

impl_rem_decimal_and_int!();
forward_ref_binop_decimal_int!(impl Rem, rem);

#[cfg(test)]
#[allow(clippy::neg_multiply)]
mod rem_integer_tests {
    use super::*;

    macro_rules! gen_rem_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i: $t = 127;
                let c = mul_pow_ten(i as i128, $p);
                let r = d % i;
                assert_eq!(r.precision(), $p);
                assert_eq!(r.coeff, $coeff - c * ($coeff / c));
                assert_eq!(r.coeff, (&d % i).coeff);
                assert_eq!(r.coeff, (d % &i).coeff);
                assert_eq!(r.coeff, (&d % &i).coeff);
                let z = i % d;
                assert_eq!(z.precision(), $p);
                assert_eq!(z.coeff, c - $coeff * (c / $coeff));
                assert_eq!(z.coeff, (&i % d).coeff);
                assert_eq!(z.coeff, (i % &d).coeff);
                assert_eq!(z.coeff, (&i % &d).coeff);
            }
        };
    }

    gen_rem_integer_tests!(test_rem_u8, u8, 2, -1);
    gen_rem_integer_tests!(test_rem_i8, i8, 0, 253);
    gen_rem_integer_tests!(test_rem_u16, u16, 4, 804);
    gen_rem_integer_tests!(test_rem_i16, i16, 4, 390625);
    gen_rem_integer_tests!(test_rem_u32, u32, 1, 1014);
    gen_rem_integer_tests!(test_rem_i32, i32, 9, -1000);
    gen_rem_integer_tests!(test_rem_u64, u64, 3, 206);
    gen_rem_integer_tests!(test_rem_i64, i64, 7, -488281250);
    gen_rem_integer_tests!(test_rem_i128, i128, 2, 1526281250433765);

    #[test]
    fn test_rem_decimal_by_int_one() {
        let x = Decimal::new_raw(17294738475, 5);
        let y = 1_i64;
        let z = x % y;
        assert_eq!(z.coeff, x.fract().coeff);
        let y = 1_u8;
        let z = x % y;
        assert_eq!(z.coeff, x.fract().coeff);
    }

    #[test]
    fn test_rem_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::new_raw(100000, 5);
        let z = x % y;
        assert_eq!(z.coeff, 0);
        let x = 1_u64;
        let z = x % y;
        assert_eq!(z.coeff, 0);
    }

    #[test]
    #[should_panic]
    fn test_rem_decimal_by_int_zero() {
        let x = Decimal::new_raw(17, 5);
        let y = 0_i32;
        let _z = x % y;
    }

    #[test]
    #[should_panic]
    fn test_rem_int_by_decimal_zero() {
        let x = 25;
        let y = Decimal::ZERO;
        let _z = x % y;
    }
}

forward_op_assign!(impl RemAssign, rem_assign, Rem, rem);

#[cfg(test)]
mod rem_assign_tests {
    use super::*;

    #[test]
    fn test_rem_assign_decimal() {
        let mut x = Decimal::new_raw(702, 3);
        let y = Decimal::new_raw(300, 2);
        x %= y;
        assert_eq!(x.coeff, 702);
        let z = Decimal::new_raw(-70, 2);
        x %= z;
        assert_eq!(x.coeff, 2);
    }

    #[test]
    fn test_rem_assign_int() {
        let mut x = Decimal::new_raw(702, 1);
        let y = 7_u16;
        x %= y;
        assert_eq!(x.coeff, 2);
        let mut x = Decimal::new_raw(-7027702, 5);
        let y = -33_i64;
        x %= y;
        assert_eq!(x.coeff, -427702);
    }
}
