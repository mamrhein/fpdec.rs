// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use crate::DivRounded;
use core::ops::Mul;

/// Rounding a number to the nearest integer multiple of a given quantum.
pub trait Quantize<Rhs = Self> {
    /// The resulting type after applying `quantize`.
    type Output;

    /// Returns an instance of `Self::Output` with its value set to the integer
    /// multiple of `quant` nearest to `self`, according to the current
    /// [RoundingMode](crate::RoundingMode).
    ///
    /// # Panics
    ///
    /// Panics if `quant` equals zero or the resulting value can not be
    /// represented by `Self::Output`!
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal, Quantize};
    /// let i = -322_i32;
    /// let q = 3_i32;
    /// let r = i.quantize(q);
    /// assert_eq!(r.to_string(), "-321");
    /// let d = Dec!(28.27093);
    /// let q = 5_u32;
    /// let r = d.quantize(q);
    /// assert_eq!(r.to_string(), "30");
    /// let q = Dec!(0.05);
    /// let r = d.quantize(q);
    /// assert_eq!(r.to_string(), "28.25");
    /// ```
    fn quantize(self, quant: Rhs) -> Self::Output;
}

impl<T, Q> Quantize<Q> for T
where
    Q: Copy,
    T: DivRounded<Q>,
    <T as DivRounded<Q>>::Output: Mul<Q>,
{
    type Output = <<T as DivRounded<Q>>::Output as Mul<Q>>::Output;

    #[inline(always)]
    fn quantize(self, quant: Q) -> Self::Output {
        self.div_rounded(quant, 0) * quant
    }
}

#[cfg(test)]
mod div_rounded_int_by_int_tests {
    use super::*;
    use crate::Decimal;

    #[test]
    fn test_quantize_int_by_int() {
        let i = 42_i32;
        let j = 15_i32;
        let q = i.quantize(j);
        assert_eq!(q.coefficient(), 45);
        assert_eq!(q.n_frac_digits(), 0);
        assert_eq!(q.coefficient(), i.quantize(&j).coefficient());
        assert_eq!(q.coefficient(), (&i).quantize(j).coefficient());
        assert_eq!(q.coefficient(), (&i).quantize(&j).coefficient());
    }

    #[test]
    fn test_quantize_int_by_dec() {
        let i = 43_u8;
        let d = Decimal::new_raw(75, 2);
        let q = i.quantize(d);
        assert_eq!(q.coefficient(), 4275);
        assert_eq!(q.n_frac_digits(), d.n_frac_digits());
        assert_eq!(q.coefficient(), i.quantize(&d).coefficient());
        assert_eq!(q.coefficient(), (&i).quantize(d).coefficient());
        assert_eq!(q.coefficient(), (&i).quantize(&d).coefficient());
    }

    #[test]
    fn test_quantize_dec_by_int() {
        let d = Decimal::new_raw(75327, 2);
        let i = 413_u64;
        let q = d.quantize(i);
        assert_eq!(q.coefficient(), 826);
        assert_eq!(q.n_frac_digits(), 0);
        assert_eq!(q.coefficient(), d.quantize(&i).coefficient());
        assert_eq!(q.coefficient(), (&d).quantize(i).coefficient());
        assert_eq!(q.coefficient(), (&d).quantize(&i).coefficient());
    }

    #[test]
    fn test_quantize_dec_by_dec() {
        let x = Decimal::new_raw(4375, 2);
        let y = Decimal::new_raw(125, 1);
        let q = x.quantize(y);
        assert_eq!(q.coefficient(), 500);
        assert_eq!(q.n_frac_digits(), y.n_frac_digits());
        let x = Decimal::new_raw(437499, 4);
        let y = Decimal::new_raw(125, 1);
        let q = x.quantize(y);
        assert_eq!(q.coefficient(), 375);
        assert_eq!(q.n_frac_digits(), y.n_frac_digits());
        assert_eq!(q.coefficient(), x.quantize(&y).coefficient());
        assert_eq!(q.coefficient(), (&x).quantize(y).coefficient());
        assert_eq!(q.coefficient(), (&x).quantize(&y).coefficient());
    }
}
