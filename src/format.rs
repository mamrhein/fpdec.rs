// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use alloc::format;
use alloc::string::{String, ToString};
use core::cmp::{min, Ordering};
use core::fmt;

use fpdec_core::{i128_div_mod_floor, i128_div_rounded, ten_pow};

use crate::Decimal;
use crate::MAX_N_FRAC_DIGITS;

impl fmt::Debug for Decimal {
    fn fmt(&self, form: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.n_frac_digits == 0 {
            write!(form, "Dec!({})", self.coefficient())
        } else {
            let (int, frac) =
                i128_div_mod_floor(self.coeff, ten_pow(self.n_frac_digits));
            write!(
                form,
                "Dec!({}.{:0width$})",
                int,
                frac,
                width = self.n_frac_digits as usize
            )
        }
    }
}

#[cfg(test)]
mod test_fmt_debug {
    use crate::Dec;

    use super::*;

    #[test]
    fn test_fmt() {
        let d = Dec!(1234567890.002);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890.002)");
        let d = Dec!(-1230.000000000);
        assert_eq!(format!("{:?}", d), "Dec!(-1230.000000000)");
        let d = Dec!(1234567890002);
        assert_eq!(format!("{:?}", d), "Dec!(1234567890002)");
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
        let prec = match form.precision() {
            Some(prec) => min(prec, MAX_N_FRAC_DIGITS as usize),
            None => self.n_frac_digits as usize,
        };
        if self.n_frac_digits == 0 {
            if prec > 0 {
                tmp =
                    format!("{}.{:0width$}", self.coeff.abs(), 0, width = prec);
            } else {
                tmp = self.coeff.abs().to_string();
            }
        } else {
            let (int, frac) = match prec.cmp(&(self.n_frac_digits as usize)) {
                Ordering::Equal => i128_div_mod_floor(
                    self.coeff.abs(),
                    ten_pow(self.n_frac_digits),
                ),
                Ordering::Less => {
                    // Important: first round, then take abs() !
                    let coeff = i128_div_rounded(
                        self.coeff,
                        ten_pow(self.n_frac_digits - prec as u8),
                        None,
                    );
                    i128_div_mod_floor(coeff.abs(), ten_pow(prec as u8))
                }
                Ordering::Greater => {
                    let (int, frac) = i128_div_mod_floor(
                        self.coeff.abs(),
                        ten_pow(self.n_frac_digits),
                    );
                    (int, frac * ten_pow(prec as u8 - self.n_frac_digits))
                }
            };
            if prec > 0 {
                tmp = format!("{}.{:0width$}", int, frac, width = prec);
            } else {
                tmp = int.to_string();
            }
        }
        form.pad_integral(self.coeff >= 0, "", &tmp)
    }
}

#[cfg(test)]
mod test_fmt_display {
    use crate::Dec;

    use super::*;

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
