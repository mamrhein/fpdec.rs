// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{cmp::min, mem};

use fpdec_core::ten_pow;

use crate::Decimal;

/// Conversion of a number into an equivalent ratio of integers.
pub trait AsIntegerRatio: Copy + Sized {
    /// Returns the pair of integers with the smallest positive denominator
    /// from those with a ratio equal to `self`.
    fn as_integer_ratio(self) -> (i128, i128) {
        (self.numerator(), self.denominator())
    }

    /// Returns the numerator from the pair of integers with the smallest
    /// positive denominator from those with a ratio equal to `self`.
    fn numerator(self) -> i128;

    /// Returns the smallest positive denominator from the pairs of integers
    /// with a ratio equal to `self`.
    fn denominator(self) -> i128;
}

impl<T> AsIntegerRatio for T
where
    T: Copy + Sized,
    i128: From<T>,
{
    #[inline(always)]
    fn numerator(self) -> i128 {
        i128::from(self)
    }

    #[inline(always)]
    fn denominator(self) -> i128 {
        1_i128
    }
}

#[cfg(test)]
mod test_int_as_ratio {
    use super::*;

    macro_rules! gen_test_as_ratio {
        ($t:ty) => {
            let i = <$t>::MAX;
            assert_eq!(i.numerator(), i128::from(i));
            assert_eq!(i.denominator(), 1_i128);
        };
    }

    #[test]
    fn test_as_ratio() {
        gen_test_as_ratio!(u8);
        gen_test_as_ratio!(i8);
        gen_test_as_ratio!(u16);
        gen_test_as_ratio!(i16);
        gen_test_as_ratio!(u32);
        gen_test_as_ratio!(i32);
        gen_test_as_ratio!(u64);
        gen_test_as_ratio!(i64);
        gen_test_as_ratio!(i128);
    }
}

// The following algorithm is a special adaptation of the binary "greatest
// common divisor" algorithm devised by Josef Stein, presented as "Algorithm
// B" in D. E. Knuth, The Art of Computer Programming, Vol. 2, Ch. 4.5.2.

/// Returns the greatest common divisor of `numer` and `10 ^ denom_exp`.
///
/// Preconditions: `numer != 0`, `denom_exp <= 38`
#[inline]
fn gcd_special(numer: i128, denom_exp: u32) -> i128 {
    assert_ne!(numer, 0);
    assert!(denom_exp <= 38);
    // Set u = |numer| with trailing zeros stripped off
    let mut u = numer.abs();
    let utz = u.trailing_zeros();
    u >>= utz;
    // Set v = denom with trailing zeros stripped off
    #[allow(clippy::cast_possible_truncation)]
    let mut v = ten_pow(denom_exp as u8) >> denom_exp;
    while v != 0 {
        v >>= v.trailing_zeros();
        if u > v {
            mem::swap(&mut u, &mut v);
        }
        // here v >= u
        v -= u;
    }
    u << min(utz, denom_exp)
}

impl AsIntegerRatio for Decimal {
    /// Returns the pair of integers with the smallest positive denominator
    /// from those with a ratio equal to `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, AsIntegerRatio};
    /// let d = Dec!(12345);
    /// assert_eq!(d.as_integer_ratio(), (12345, 1));
    /// let d = Dec!(28.27095);
    /// assert_eq!(d.as_integer_ratio(), (565419, 20000));
    /// ```
    #[allow(clippy::integer_division)]
    fn as_integer_ratio(self) -> (i128, i128) {
        if self.n_frac_digits == 0 || self.coeff == 0 {
            // self is equivalent to an integer
            return (self.coeff, 1);
        }
        let gcd = gcd_special(self.coeff, self.n_frac_digits as u32);
        (self.coeff / gcd, self.denominator())
    }

    /// Returns the numerator from the pair of integers with the smallest
    /// positive denominator from those with a ratio equal to `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, AsIntegerRatio};
    /// let d = Dec!(12345.0);
    /// assert_eq!(d.numerator(), 12345);
    /// let d = Dec!(28.27095);
    /// assert_eq!(d.numerator(), 565419);
    /// ```
    #[allow(clippy::integer_division)]
    fn numerator(self) -> i128 {
        if self.n_frac_digits == 0 || self.coeff == 0 {
            // self is equivalent to an integer
            return self.coeff;
        }
        let gcd = gcd_special(self.coeff, self.n_frac_digits as u32);
        self.coeff / gcd
    }

    /// Returns the smallest positive denominator from the pairs of integers
    /// with a ratio equal to `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, AsIntegerRatio};
    /// let d = Dec!(12345.00);
    /// assert_eq!(d.denominator(), 1);
    /// let d = Dec!(28.27095);
    /// assert_eq!(d.denominator(), 20000);
    /// ```
    #[allow(clippy::integer_division)]
    fn denominator(self) -> i128 {
        if self.n_frac_digits == 0 || self.coeff == 0 {
            // self is equivalent to an integer
            return 1;
        }
        let gcd = gcd_special(self.coeff, self.n_frac_digits as u32);
        ten_pow(self.n_frac_digits) / gcd
    }
}

#[cfg(test)]
mod test_decimal_as_ratio {
    use fpdec_core::MAX_N_FRAC_DIGITS;

    use super::*;

    #[test]
    fn test_decimal_as_ratio() {
        let d = Decimal::new_raw(0, MAX_N_FRAC_DIGITS);
        assert_eq!(d.as_integer_ratio(), (0, 1));
        let d = Decimal::new_raw(12345, 0);
        assert_eq!(d.as_integer_ratio(), (12345, 1));
        let d = Decimal::new_raw(12345, 4);
        assert_eq!(d.as_integer_ratio(), (12345 / 5, ten_pow(4) / 5));
        let d = Decimal::new_raw(123456, 4);
        assert_eq!(d.as_integer_ratio(), (123456 / 16, ten_pow(4) / 16));
        let d = Decimal::new_raw(1234567, 4);
        assert_eq!(d.as_integer_ratio(), (1234567, ten_pow(4)));
        let d = Decimal::new_raw(12345678, 9);
        assert_eq!(d.as_integer_ratio(), (12345678 / 2, ten_pow(9) / 2));
    }

    #[test]
    fn test_decimal_numerator() {
        let d = Decimal::new_raw(0, MAX_N_FRAC_DIGITS);
        assert_eq!(d.numerator(), 0);
        let d = Decimal::new_raw(12345, 0);
        assert_eq!(d.numerator(), 12345);
        let d = Decimal::new_raw(12345, 4);
        assert_eq!(d.numerator(), 12345 / 5);
        let d = Decimal::new_raw(123456, 4);
        assert_eq!(d.numerator(), 123456 / 16);
        let d = Decimal::new_raw(1234567, 4);
        assert_eq!(d.numerator(), 1234567);
        let d = Decimal::new_raw(12345678, 9);
        assert_eq!(d.numerator(), 12345678 / 2);
    }

    #[test]
    fn test_decimal_denominator() {
        let d = Decimal::new_raw(0, MAX_N_FRAC_DIGITS);
        assert_eq!(d.denominator(), 1);
        let d = Decimal::new_raw(12345, 0);
        assert_eq!(d.denominator(), 1);
        let d = Decimal::new_raw(12345, 4);
        assert_eq!(d.denominator(), ten_pow(4) / 5);
        let d = Decimal::new_raw(123456, 4);
        assert_eq!(d.denominator(), ten_pow(4) / 16);
        let d = Decimal::new_raw(1234567, 4);
        assert_eq!(d.denominator(), ten_pow(4));
        let d = Decimal::new_raw(12345678, 9);
        assert_eq!(d.denominator(), ten_pow(9) / 2);
    }
}
