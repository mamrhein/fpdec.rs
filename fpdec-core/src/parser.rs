// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::{
    fmt::{Display, Formatter},
    ptr,
};

/// An error which can be returned when parsing a decimal literal.
///
/// This error is used as the error type for the `FromStr` implementation of
/// `Decimal`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseDecimalError {
    /// An empty string has been given as literal.
    Empty,
    /// The given string is not a valid decimal literal.
    Invalid,
    /// The given decimal literal has more fractional digits than specified by
    /// `MAX_N_FRAC_DIGITS`.
    FracDigitLimitExceeded,
    /// The given decimal literal would exceed the internal representation of
    /// `Decimal`.
    InternalOverflow,
}

impl ParseDecimalError {
    #[doc(hidden)]
    pub fn _description(&self) -> &str {
        match self {
            ParseDecimalError::Empty => "Empty string.",
            ParseDecimalError::Invalid => "Invalid decimal string literal.",
            ParseDecimalError::FracDigitLimitExceeded => {
                "Too many fractional digits."
            }
            ParseDecimalError::InternalOverflow => {
                "Internal representation exceeded."
            }
        }
    }
}

impl Display for ParseDecimalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Display::fmt(self._description(), f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseDecimalError {}

/// Check whether an u64 is holding 8 decimal digits.
fn chunk_contains_8_digits(chunk: u64) -> bool {
    // Subtract b'0' from each byte.
    let x = chunk.wrapping_sub(0x3030303030303030);
    // Add 0x46 (= 0x7f - b'9') to each byte.
    let y = chunk.wrapping_add(0x4646464646464646);
    // In x now all original bytes < b'0' have the highest bit set, and
    // in y now all original bytes > b'9' are > 0x7f.
    // Then, in x|y all original bytes besides b'0' .. b'9' are > 0x7f.
    // Thus, bitwise-and with 0x80 gives 0 for all original bytes b'0' .. b'9'
    // and 0x7f for all others.
    (x | y) & 0x8080808080808080 == 0
}

/// Convert an u64 holding a sequence of 8 decimal digits into an u64.
fn chunk_to_u64(mut chunk: u64) -> u64 {
    // The following is adopted from Johnny Lee: Fast numeric string to int
    // [https://johnnylee-sde.github.io/Fast-numeric-string-to-int].
    chunk &= 0x0f0f0f0f0f0f0f0f;
    chunk = (chunk & 0x000f000f000f000f)
        .wrapping_mul(10)
        .wrapping_add((chunk >> 8) & 0x000f000f000f000f);
    chunk = (chunk & 0x0000007f0000007f)
        .wrapping_mul(100)
        .wrapping_add((chunk >> 16) & 0x0000007f0000007f);
    (chunk & 0x3fff)
        .wrapping_mul(10000)
        .wrapping_add((chunk >> 32) & 0x3fff)
}

// Bytes wrapper specialized for parsing decimal number literals
struct AsciiDecLit<'a> {
    bytes: &'a [u8],
}

impl<'a> AsciiDecLit<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    fn len(&self) -> usize {
        self.bytes.len()
    }

    /// self <- self[n..]
    unsafe fn skip_n(&mut self, n: usize) -> &mut Self {
        debug_assert!(self.bytes.len() >= n);
        self.bytes = self.bytes.get_unchecked(n..);
        self
    }

    /// self <- self[n..]
    unsafe fn skip_1(&mut self) -> &mut Self {
        self.skip_n(1)
    }

    fn first(&self) -> Option<&u8> {
        self.bytes.first()
    }

    fn first_eq(&self, b: u8) -> bool {
        Some(&b) == self.first()
    }

    fn first_is_digit(&self) -> bool {
        match self.first() {
            Some(c) if c.wrapping_sub(b'0') < 10 => true,
            _ => false,
        }
    }

    fn skip_leading_zeroes(&mut self) -> &mut Self {
        while self.first_eq(b'0') {
            // safe because of condition above!
            unsafe {
                self.skip_1();
            };
        }
        self
    }

    // Read 8 bytes as u64 (little-endian).
    unsafe fn read_u64_unchecked(&self) -> u64 {
        debug_assert!(self.bytes.len() >= 8);
        let src = self.bytes.as_ptr() as *const u64;
        u64::from_le(ptr::read_unaligned(src))
    }

    // Try to read the next 8 bytes from self.
    fn read_u64(&self) -> Option<u64> {
        if self.len() >= 8 {
            // safe because of condition above!
            Some(unsafe { self.read_u64_unchecked() })
        } else {
            None
        }
    }

    /// Convert the leading sequence of decimal digits in `self` (if any) into
    /// an int and accumulate it into `coeff`.
    // The function uses wrapping_mul and wrapping_add, so overflow can happen;
    // it must be checked later!
    fn accum_coeff(&mut self, coeff: &mut u128) -> usize {
        let start_len = self.len();
        // First, try chunks of 8 digits
        while let Some(k) = self.read_u64() {
            if chunk_contains_8_digits(k) {
                *coeff = coeff
                    .wrapping_mul(100000000)
                    .wrapping_add(chunk_to_u64(k) as u128);
                // safe because of call to self.read_u64 above
                unsafe {
                    self.skip_n(8);
                }
            } else {
                break;
            }
        }
        // Handle remaining digits
        while let Some(c) = self.first() {
            let d = c.wrapping_sub(b'0');
            if d < 10 {
                *coeff = coeff.wrapping_mul(10).wrapping_add(d as u128);
                // safe because of call to self.first above
                unsafe {
                    self.skip_1();
                }
            } else {
                break;
            }
        }
        start_len - self.len()
    }

    /// Convert the leading sequence of decimal digits in `self` (if any) into
    /// an int and accumulate it into `exp`.
    // The function uses wrapping_mul and wrapping_add, but overflow is
    // prevented by limiting the result to a value which will cause an error
    // later!
    fn accum_exp(&mut self, exp: &mut isize) -> usize {
        let start_len = self.len();
        while let Some(c) = self.first() {
            let d = c.wrapping_sub(b'0');
            if d < 10 {
                if *exp < 0x1000000 {
                    *exp = exp.wrapping_mul(10).wrapping_add(d as isize);
                }
                // safe because of call to self.first above
                unsafe {
                    self.skip_1();
                }
            } else {
                break;
            }
        }
        start_len - self.len()
    }
}

/// Convert a decimal number literal into a representation in the form
/// (coefficient, exponent), so that number == coefficient * 10 ^ exponent.
///
/// The literal must be in the form
///
/// `[+|-]<int>[.<frac>][<e|E>[+|-]<exp>]`
///
/// or
///
/// `[+|-].<frac>[<e|E>[+|-]<exp>]`.
#[doc(hidden)]
pub fn str_to_dec(lit: &str) -> Result<(i128, isize), ParseDecimalError> {
    let mut lit = AsciiDecLit::new(lit.as_ref());
    let is_negative = match lit.first() {
        None => {
            return Err(ParseDecimalError::Empty);
        }
        Some(&c) if c == b'-' => {
            // safe because of match
            unsafe { lit.skip_1() };
            true
        }
        Some(&c) if c == b'+' => {
            // safe because of match
            unsafe { lit.skip_1() };
            false
        }
        _ => false,
    };
    if lit.is_empty() {
        return Err(ParseDecimalError::Invalid);
    }
    lit.skip_leading_zeroes();
    if lit.is_empty() {
        // There must have been atleast one zero. Ignore sign.
        return Ok((0, 0));
    }
    let mut coeff = 0_u128;
    // Parse integral digits.
    let n_int_digits = lit.accum_coeff(&mut coeff);
    // Check for radix point and parse fractional digits.
    let mut n_frac_digits = 0_usize;
    if let Some(c) = lit.first() {
        if *c == b'.' {
            // safe because of condition above
            unsafe { lit.skip_1() };
            n_frac_digits = lit.accum_coeff(&mut coeff);
        }
    }
    let n_digits = n_int_digits + n_frac_digits;
    if n_digits == 0 {
        return Err(ParseDecimalError::Invalid);
    }
    // check for overflow
    // 1. 10^e > i128::MAX for e > 39
    // 2. e = 39 && coeff < i128::MAX (overflow occured during accumulation)
    // 3. coeff > i128::MAX
    if n_digits > 39
        || n_digits == 39 && coeff < i128::MAX as u128
        || coeff > i128::MAX as u128
    {
        return Err(ParseDecimalError::InternalOverflow);
    }
    let mut exp = 0_isize;
    // check for explicit exponent
    if let Some(c) = lit.first() {
        if *c == b'e' || *c == b'E' {
            // safe because of condition above
            unsafe { lit.skip_1() };
            let exp_is_negative = match lit.first() {
                None => {
                    return Err(ParseDecimalError::Invalid);
                }
                Some(&c) if c == b'-' => {
                    // safe because of match
                    unsafe { lit.skip_1() };
                    true
                }
                Some(&c) if c == b'+' => {
                    // safe because of match
                    unsafe { lit.skip_1() };
                    false
                }
                _ => false,
            };
            let n_exp_digits = lit.accum_exp(&mut exp);
            if exp_is_negative {
                exp = -exp;
            }
            if n_exp_digits > 2 {
                return Err(ParseDecimalError::FracDigitLimitExceeded);
            }
        } else {
            return Err(ParseDecimalError::Invalid);
        }
    }
    if !lit.is_empty() {
        return Err(ParseDecimalError::Invalid);
    }
    exp -= n_frac_digits as isize;
    if -exp > crate::MAX_N_FRAC_DIGITS as isize {
        return Err(ParseDecimalError::FracDigitLimitExceeded);
    }
    if is_negative {
        Ok((-(coeff as i128), exp))
    } else {
        Ok((coeff as i128, exp))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // use crate::str2dec;

    #[test]
    fn test_parse_int_lit() {
        let res = str_to_dec("1957945").unwrap();
        assert_eq!(res, (1957945, 0));
    }

    #[test]
    fn test_parse_dec_lit() {
        let res = str_to_dec("-17.5").unwrap();
        assert_eq!(res, (-175, -1));
    }

    #[test]
    fn test_parse_frac_only_lit() {
        let res = str_to_dec("+.75").unwrap();
        assert_eq!(res, (75, -2));
    }

    #[test]
    fn test_parse_int_lit_neg_exp() {
        let res = str_to_dec("17e-5").unwrap();
        assert_eq!(res, (17, -5));
    }

    #[test]
    fn test_parse_int_lit_pos_exp() {
        let res = str_to_dec("+217e3").unwrap();
        assert_eq!(res, (217, 3));
    }

    #[test]
    fn test_parse_dec_lit_neg_exp() {
        let res = str_to_dec("-533.7e-2").unwrap();
        assert_eq!(res, (-5337, -3));
    }

    #[test]
    fn test_parse_dec_lit_pos_exp() {
        let res = str_to_dec("700004.002E13").unwrap();
        assert_eq!(res, (700004002, 10));
    }

    #[test]
    fn test_err_empty_str() {
        let res = str_to_dec("");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::Empty);
    }

    #[test]
    fn test_err_invalid_lit() {
        let lits = [" ", "+", "-4.33.2", "2.87 e3", "+e3", ".4e3 "];
        for lit in lits {
            let res = str_to_dec(lit);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, ParseDecimalError::Invalid);
        }
    }

    #[test]
    fn test_frac_limit_exceeded() {
        let res = str_to_dec("0.17295887390016377542");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_frac_limit_exceeded_with_exp() {
        let res = str_to_dec("17.493e-36");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_int_lit_max_val_exceeded() {
        let s = "170141183460469231731687303715884105728";
        let res = str_to_dec(s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::InternalOverflow);
    }

    #[test]
    fn test_dec_lit_max_val_exceeded() {
        let s = "1701411834604692317316873037158841058.00";
        let res = str_to_dec(s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::InternalOverflow);
    }
}
