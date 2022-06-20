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
    ops::{Rem, RemAssign},
};

use fpdec_core::checked_mul_pow_ten;

use crate::{Decimal, DecimalError};

#[inline]
pub(crate) fn rem(
    divident_coeff: i128,
    divident_n_frac_digits: u8,
    divisor_coeff: i128,
    divisor_n_frac_digits: u8,
) -> Result<(i128, u8), DecimalError> {
    match divident_n_frac_digits.cmp(&divisor_n_frac_digits) {
        Ordering::Equal => {
            Ok((divident_coeff % divisor_coeff, divident_n_frac_digits))
        }
        Ordering::Greater => match checked_mul_pow_ten(
            divisor_coeff,
            divident_n_frac_digits - divisor_n_frac_digits,
        ) {
            Some(shifted_divisor_coeff) => Ok((
                divident_coeff % shifted_divisor_coeff,
                divident_n_frac_digits,
            )),
            None => Ok((divident_coeff, divident_n_frac_digits)),
        },
        Ordering::Less => {
            let mut shift = divisor_n_frac_digits - divident_n_frac_digits;
            match checked_mul_pow_ten(divident_coeff, shift) {
                Some(shifted_divident_coeff) => Ok((
                    shifted_divident_coeff % divisor_coeff,
                    divisor_n_frac_digits,
                )),
                None => {
                    let mut rem = divident_coeff % divisor_coeff;
                    while rem != 0 && shift > 0 {
                        match rem.checked_mul(10) {
                            Some(shifted_rem) => {
                                rem = shifted_rem % divisor_coeff;
                            }
                            None => return Err(DecimalError::InternalOverflow),
                        }
                        shift -= 1;
                    }
                    Ok((rem, divisor_n_frac_digits))
                }
            }
        }
    }
}

impl Rem<Decimal> for Decimal {
    type Output = Decimal;

    fn rem(self, rhs: Decimal) -> Self::Output {
        if rhs.eq_zero() {
            panic!("{}", DecimalError::DivisionByZero);
        }
        if self.eq_zero() {
            return Self::ZERO;
        }
        if rhs.eq_one() {
            return self.fract();
        }
        match rem(self.coeff, self.n_frac_digits, rhs.coeff, rhs.n_frac_digits)
        {
            Ok((coeff, n_frac_digits)) => Self::Output {
                coeff,
                n_frac_digits,
            },
            Err(error) => panic!("{}", error),
        }
    }
}

forward_ref_binop!(impl Rem, rem);

#[cfg(test)]
mod rem_decimal_tests {
    use super::*;

    #[test]
    fn test_rem_same_n_frac_digits() {
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(300, 2);
        let r = x % y;
        assert_eq!(r.coefficient(), 102);
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(-307, 2);
        let r = x % y;
        assert_eq!(r.coefficient(), 88);
        let x = Decimal::new_raw(-702, 2);
        let y = Decimal::new_raw(307, 2);
        let r = x % y;
        assert_eq!(r.coefficient(), -88);
    }

    #[test]
    fn test_rem_diff_n_frac_digits() {
        let x = Decimal::new_raw(702, 3);
        let y = Decimal::new_raw(300, 2);
        let r = x % y;
        assert_eq!(r.coefficient(), 702);
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::new_raw(-307, 5);
        let r = x % y;
        assert_eq!(r.coefficient(), 198);
        let x = Decimal::new_raw(-702, 2);
        let y = Decimal::new_raw(307, 4);
        let r = x % y;
        assert_eq!(r.coefficient(), -204);
    }

    #[test]
    fn test_rem_by_one() {
        let x = Decimal::new_raw(702, 2);
        let y = Decimal::ONE;
        let r = x % y;
        assert_eq!(r.coefficient(), x.fract().coefficient());
        assert_eq!(r.n_frac_digits(), x.n_frac_digits());
        let x = Decimal::new_raw(70389032, 4);
        let y = Decimal::new_raw(100000, 5);
        let r = x % y;
        assert_eq!(r.coefficient(), x.fract().coefficient());
        assert_eq!(r.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    fn test_rem_rhs_shift_ovfl() {
        let x = Decimal::new_raw(i128::MAX, 2);
        let y = Decimal::new_raw(i128::MAX / 5, 1);
        let r = x % y;
        assert_eq!(r.coefficient(), x.coefficient());
        assert_eq!(r.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    fn test_rem_lhs_shift_ovfl() {
        let x = Decimal::new_raw(i128::MAX / 30, 1);
        let y = Decimal::new_raw(i128::MAX / 500, 3);
        let r = x % y;
        assert_eq!(r.coefficient(), 226854911280625642308916404954512874_i128);
        assert_eq!(r.n_frac_digits(), y.n_frac_digits());
    }

    #[test]
    #[should_panic]
    fn test_rem_panic_ovfl() {
        let x = Decimal::new_raw(i128::MAX / 3, 1);
        let y = Decimal::new_raw(i128::MAX / 5, 3);
        let _r = x % y;
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

            fn rem(self, rhs: $t) -> Self::Output {
                if rhs == 0 {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self.eq_zero() {
                    return Self::ZERO;
                }
                if rhs == 1 {
                    return self.fract();
                }
                match rem(
                    self.coeff,
                    self.n_frac_digits(),
                    i128::from(rhs),
                    0,
                ) {
                    Ok((coeff, n_frac_digits)) => Self::Output {
                        coeff,
                        n_frac_digits,
                    },
                    Err(error) => panic!("{}", error),
                }
            }
        }

        impl Rem<Decimal> for $t {
            type Output = Decimal;

            fn rem(self, rhs: Decimal) -> Self::Output {
                if rhs.eq_zero() {
                    panic!("{}", DecimalError::DivisionByZero);
                }
                if self == 0 || rhs.eq_one(){
                    return Decimal::ZERO;
                }
                match rem(
                    i128::from(self),
                    0,
                    rhs.coeff,
                    rhs.n_frac_digits(),
                ) {
                    Ok((coeff, n_frac_digits)) => Self::Output {
                        coeff,
                        n_frac_digits,
                    },
                    Err(error) => panic!("{}", error),
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
    use fpdec_core::mul_pow_ten;

    use super::*;

    macro_rules! gen_rem_integer_tests {
        ($func:ident, $t:ty, $p:expr, $coeff:expr) => {
            #[test]
            fn $func() {
                let d = Decimal::new_raw($coeff, $p);
                let i: $t = 127;
                let c = mul_pow_ten(i128::from(i), $p);
                let r = d % i;
                assert_eq!(r.n_frac_digits(), $p);
                assert_eq!(r.coefficient(), $coeff - c * ($coeff / c));
                assert_eq!(r.coefficient(), (&d % i).coefficient());
                assert_eq!(r.coefficient(), (d % &i).coefficient());
                assert_eq!(r.coefficient(), (&d % &i).coefficient());
                let z = i % d;
                assert_eq!(z.n_frac_digits(), $p);
                assert_eq!(z.coefficient(), c - $coeff * (c / $coeff));
                assert_eq!(z.coefficient(), (&i % d).coefficient());
                assert_eq!(z.coefficient(), (i % &d).coefficient());
                assert_eq!(z.coefficient(), (&i % &d).coefficient());
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
        assert_eq!(z.coefficient(), x.fract().coefficient());
        let y = 1_u8;
        let z = x % y;
        assert_eq!(z.coefficient(), x.fract().coefficient());
    }

    #[test]
    fn test_rem_int_by_decimal_one() {
        let x = 17_i32;
        let y = Decimal::new_raw(100000, 5);
        let z = x % y;
        assert_eq!(z.coefficient(), 0);
        let x = 1_u64;
        let z = x % y;
        assert_eq!(z.coefficient(), 0);
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

    #[test]
    fn test_rem_rhs_shift_ovfl() {
        let x = Decimal::new_raw(i128::MAX, 2);
        let y = i128::MAX / 5;
        let r = x % y;
        assert_eq!(r.coefficient(), x.coefficient());
        assert_eq!(r.n_frac_digits(), x.n_frac_digits());
    }

    #[test]
    fn test_rem_lhs_shift_ovfl() {
        let x = i128::MAX / 30;
        let y = Decimal::new_raw(i128::MAX / 500, 2);
        let r = x % y;
        assert_eq!(r.coefficient(), 226854911280625642308916404954512874_i128);
        assert_eq!(r.n_frac_digits(), y.n_frac_digits());
    }

    #[test]
    #[should_panic]
    fn test_rem_panic_ovfl() {
        let x = i128::MAX / 3;
        let y = Decimal::new_raw(i128::MAX / 5, 3);
        let _r = x % y;
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
        assert_eq!(x.coefficient(), 702);
        let z = Decimal::new_raw(-70, 2);
        x %= z;
        assert_eq!(x.coefficient(), 2);
    }

    #[test]
    fn test_rem_assign_int() {
        let mut x = Decimal::new_raw(702, 1);
        let y = 7_u16;
        x %= y;
        assert_eq!(x.coefficient(), 2);
        let mut x = Decimal::new_raw(-7027702, 5);
        let y = -33_i64;
        x %= y;
        assert_eq!(x.coefficient(), -427702);
    }
}
