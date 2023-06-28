// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use alloc::{
    format,
    string::{String, ToString},
};
use core::{
    cmp::{min, Ordering},
    fmt,
};

use fpdec_core::{i128_div_mod_floor, i128_div_rounded, ten_pow};

#[cfg(feature = "rkyv")]
use crate::ArchivedDecimal;
use crate::{Decimal, MAX_N_FRAC_DIGITS};

impl From<Decimal> for String {
    fn from(d: Decimal) -> Self {
        if d.n_frac_digits == 0 {
            format!("{}", d.coefficient())
        } else {
            let (int, frac) =
                i128_div_mod_floor(d.coeff.abs(), ten_pow(d.n_frac_digits));
            format!(
                "{}{}.{:0width$}",
                if d.coeff >= 0 { "" } else { "-" },
                int,
                frac,
                width = d.n_frac_digits() as usize
            )
        }
    }
}

#[cfg(test)]
mod test_into_string {
    use super::*;
    use crate::Dec;

    #[test]
    fn test_into_string() {
        let d = Decimal::MIN;
        let s: String = d.into();
        assert_eq!(s, format!("{}", i128::MIN + 1));
        let d = Decimal::MAX;
        let s: String = d.into();
        assert_eq!(s, format!("{}", i128::MAX));
        let d = Dec!(-1234567890123456789000.00700);
        let s: String = d.into();
        assert_eq!(s, "-1234567890123456789000.00700");
    }
}

macro_rules! impl_debug {
    ($ty:ty, $tag:literal) => {
        impl fmt::Debug for $ty {
            fn fmt(&self, form: &mut fmt::Formatter<'_>) -> fmt::Result {
                if self.n_frac_digits == 0 {
                    write!(form, concat!($tag, "({})"), self.coefficient())
                } else {
                    let (int, frac) = i128_div_mod_floor(
                        self.coeff.abs(),
                        ten_pow(self.n_frac_digits),
                    );
                    write!(
                        form,
                        concat!($tag, "({}{}.{:0width$})"),
                        if self.coeff >= 0 { "" } else { "-" },
                        int,
                        frac,
                        width = self.n_frac_digits as usize
                    )
                }
            }
        }
    };
}

impl_debug!(Decimal, "Dec!");
#[cfg(feature = "rkyv")]
impl_debug!(ArchivedDecimal, "ArchivedDecimal");

#[cfg(test)]
mod test_fmt_debug {
    use super::*;
    use crate::Dec;

    #[test]
    fn test_fmt() {
        let d = Dec!(-1234567890.002);
        assert_eq!(format!("{:?}", d), "Dec!(-1234567890.002)");
        let d = Dec!(1230.000000000);
        assert_eq!(format!("{:?}", d), "Dec!(1230.000000000)");
        let d = Dec!(1234567890002);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890002)");
    }

    #[test]
    fn test_issue_6() {
        let d = Decimal::new_raw(-4247228607487600, 18);
        let s = format!(concat!("Dec!", "({})"), d);
        let t = format!("{d:?}");
        assert_eq!(t, s);
    }
}

impl fmt::Display for Decimal {
    /// Formats the value using the given formatter.
    ///
    /// If the format specifies less fractional digits than
    /// `self.n_frac_digits()`, the value gets rounded according to the
    /// default rounding mode.
    ///
    /// # Examples:
    ///
    /// ```rust
    /// # use core::fmt;
    /// # use fpdec::{Dec, Decimal};
    /// let d = Dec!(-1234.56);
    /// assert_eq!(format!("{}", d), "-1234.56");
    /// assert_eq!(format!("{:014.3}", d), "-000001234.560");
    /// assert_eq!(format!("{:10.1}", d), "   -1234.6");
    /// ```
    fn fmt(&self, form: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tmp: String;
        #[allow(clippy::cast_possible_truncation)]
        let prec = match form.precision() {
            Some(prec) => min(prec, MAX_N_FRAC_DIGITS as usize) as u8,
            None => self.n_frac_digits,
        };
        if self.n_frac_digits == 0 {
            if prec > 0 {
                tmp = format!(
                    "{}.{:0width$}",
                    self.coeff.abs(),
                    0,
                    width = prec as usize
                );
            } else {
                tmp = self.coeff.abs().to_string();
            }
        } else {
            let (int, frac) = match prec.cmp(&(self.n_frac_digits)) {
                Ordering::Equal => i128_div_mod_floor(
                    self.coeff.abs(),
                    ten_pow(self.n_frac_digits),
                ),
                Ordering::Less => {
                    // Important: first round, then take abs() !
                    let coeff = i128_div_rounded(
                        self.coeff,
                        ten_pow(self.n_frac_digits - prec),
                        None,
                    );
                    i128_div_mod_floor(coeff.abs(), ten_pow(prec))
                }
                Ordering::Greater => {
                    let (int, frac) = i128_div_mod_floor(
                        self.coeff.abs(),
                        ten_pow(self.n_frac_digits),
                    );
                    (int, frac * ten_pow(prec - self.n_frac_digits))
                }
            };
            if prec > 0 {
                tmp = format!(
                    "{}.{:0width$}",
                    int,
                    frac,
                    width = prec as usize
                );
            } else {
                tmp = int.to_string();
            }
        }
        form.pad_integral(self.coeff >= 0, "", &tmp)
    }
}

#[cfg(test)]
mod test_fmt_display {
    use super::*;
    use crate::Dec;

    #[test]
    fn test_fmt_integral_decimal() {
        let d = Dec!(1234567890002);
        assert_eq!(d.to_string(), "1234567890002");
        assert_eq!(format!("{}", d), "1234567890002");
        assert_eq!(format!("{:<15}", d), "1234567890002  ");
        assert_eq!(format!("{:^15}", d), " 1234567890002 ");
        assert_eq!(format!("{:>15}", d), "  1234567890002");
        assert_eq!(format!("{:15}", d), "  1234567890002");
        assert_eq!(format!("{:015}", d), "001234567890002");
        assert_eq!(format!("{:010.2}", d), "1234567890002.00");
        let d = Dec!(-12345);
        assert_eq!(d.to_string(), "-12345");
        assert_eq!(format!("{}", d), "-12345");
        assert_eq!(format!("{:10}", d), "    -12345");
        assert_eq!(format!("{:010}", d), "-000012345");
        assert_eq!(format!("{:012.3}", d), "-0012345.000");
    }

    #[test]
    fn test_fmt_decimal_without_rounding() {
        let d = Dec!(123456789.0002);
        assert_eq!(d.to_string(), "123456789.0002");
        assert_eq!(format!("{}", d), "123456789.0002");
        assert_eq!(format!("{:<15}", d), "123456789.0002 ");
        assert_eq!(format!("{:^17}", d), " 123456789.0002  ");
        assert_eq!(format!("{:>15}", d), " 123456789.0002");
        assert_eq!(format!("{:15}", d), " 123456789.0002");
        assert_eq!(format!("{:015}", d), "0123456789.0002");
        assert_eq!(format!("{:010.7}", d), "123456789.0002000");
        let d = Dec!(-123.45);
        assert_eq!(d.to_string(), "-123.45");
        assert_eq!(format!("{}", d), "-123.45");
        assert_eq!(format!("{:10}", d), "   -123.45");
        assert_eq!(format!("{:010}", d), "-000123.45");
        assert_eq!(format!("{:012.3}", d), "-0000123.450");
        let d = Dec!(-0.0012345);
        assert_eq!(d.to_string(), "-0.0012345");
        assert_eq!(format!("{}", d), "-0.0012345");
    }

    #[test]
    fn test_fmt_decimal_with_rounding() {
        let d = Dec!(12345678.90002);
        assert_eq!(format!("{:.4}", d), "12345678.9000");
        assert_eq!(format!("{:<15.2}", d), "12345678.90    ");
        assert_eq!(format!("{:.0}", d), "12345679");
        let d = Dec!(-0.0012347);
        assert_eq!(format!("{:.3}", d), "-0.001");
        assert_eq!(format!("{:10.5}", d), "  -0.00123");
        assert_eq!(format!("{:010.6}", d), "-00.001235");
    }
}
