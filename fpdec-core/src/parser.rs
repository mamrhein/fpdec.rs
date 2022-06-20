// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use core::fmt::{Display, Formatter};

use crate::powers_of_ten::checked_mul_pow_ten;

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

struct DecLitParts<'a> {
    num_sign: &'a str,
    int_part: &'a str,
    frac_part: &'a str,
    exp_sign: &'a str,
    exp_part: &'a str,
}

/// Parse a Decimal literal in the form
/// \[+|-]<int>\[.<frac>]\[<e|E>\[+|-]<exp>] or
/// \[+|-].<frac>\[<e|E>\[+|-]<exp>].
fn parse_decimal_literal(lit: &str) -> Result<DecLitParts, ParseDecimalError> {
    let mut num_sign_range = 0usize..0usize;
    let mut int_part_range = 0usize..0usize;
    let mut frac_part_range = 0usize..0usize;
    let mut exp_sign_range = 0usize..0usize;
    let mut exp_part_range = 0usize..0usize;
    let mut chars = lit.char_indices();
    let mut next = chars.next();
    if next.is_none() {
        return Result::Err(ParseDecimalError::Empty);
    }
    let (mut curr_idx, mut curr_char) = next.unwrap();
    if curr_char == '-' || curr_char == '+' {
        num_sign_range = curr_idx..curr_idx + 1;
        next = chars.next();
    }
    int_part_range.start = num_sign_range.end;
    loop {
        match next {
            None => {
                curr_idx = lit.len();
                if int_part_range.start < curr_idx {
                    int_part_range.end = lit.len();
                    return Ok(DecLitParts {
                        num_sign: &lit[num_sign_range],
                        int_part: &lit[int_part_range],
                        frac_part: "",
                        exp_sign: "",
                        exp_part: "",
                    });
                } else {
                    return Result::Err(ParseDecimalError::Invalid);
                }
            }
            Some((idx, ch)) => {
                if !ch.is_ascii_digit() {
                    int_part_range.end = idx;
                    curr_char = ch;
                    curr_idx = idx;
                    break;
                }
            }
        }
        next = chars.next();
    }
    if curr_char == '.' {
        frac_part_range.start = curr_idx + 1;
        next = chars.next();
        loop {
            match next {
                None => {
                    frac_part_range.end = lit.len();
                    return Ok(DecLitParts {
                        num_sign: &lit[num_sign_range],
                        int_part: &lit[int_part_range],
                        frac_part: &lit[frac_part_range],
                        exp_sign: "",
                        exp_part: "",
                    });
                }
                Some((idx, ch)) => {
                    if !ch.is_ascii_digit() {
                        frac_part_range.end = idx;
                        curr_char = ch;
                        break;
                    }
                }
            }
            next = chars.next();
        }
    }
    if curr_char == 'e' || curr_char == 'E' {
        next = chars.next();
        if next.is_none() {
            return Result::Err(ParseDecimalError::Invalid);
        }
        let (curr_idx, curr_char) = next.unwrap();
        if curr_char == '-' || curr_char == '+' {
            exp_sign_range = curr_idx..curr_idx + 1;
            exp_part_range.start = curr_idx + 1;
        } else if curr_char.is_ascii_digit() {
            exp_part_range.start = curr_idx;
        } else {
            return Result::Err(ParseDecimalError::Invalid);
        }
        next = chars.next();
        loop {
            match next {
                None => {
                    exp_part_range.end = lit.len();
                    break;
                }
                Some((_, ch)) => {
                    if !ch.is_ascii_digit() {
                        return Result::Err(ParseDecimalError::Invalid);
                    }
                }
            }
            next = chars.next();
        }
    } else {
        return Result::Err(ParseDecimalError::Invalid);
    }
    if int_part_range.is_empty() && frac_part_range.is_empty() {
        return Result::Err(ParseDecimalError::Invalid);
    }
    Ok(DecLitParts {
        num_sign: &lit[num_sign_range],
        int_part: &lit[int_part_range],
        frac_part: &lit[frac_part_range],
        exp_sign: &lit[exp_sign_range],
        exp_part: &lit[exp_part_range],
    })
}

/// Convert a decimal number literal into a representation in the form
/// (coefficient, exponent), so that number == coefficient * 10 ^ exponent.
///
/// The literal must be in the form
/// \[+|-]<int>\[.<frac>]\[<e|E>\[+|-]<exp>] or
/// \[+|-].<frac>\[<e|E>\[+|-]<exp>].
#[doc(hidden)]
pub fn dec_repr_from_str(
    lit: &str,
) -> Result<(i128, isize), ParseDecimalError> {
    let max_n_frac_digits = crate::MAX_N_FRAC_DIGITS as isize;
    let parts = parse_decimal_literal(lit)?;
    let exp: isize = if !parts.exp_part.is_empty() {
        if parts.exp_sign == "-" {
            -parts.exp_part.parse::<isize>().unwrap()
        } else {
            parts.exp_part.parse().unwrap()
        }
    } else {
        0
    };
    let n_frac_digits = parts.frac_part.len() as isize;
    if n_frac_digits - exp > max_n_frac_digits {
        return Result::Err(ParseDecimalError::FracDigitLimitExceeded);
    }
    let mut coeff: i128 = if !parts.int_part.is_empty() {
        match parts.int_part.parse() {
            Err(_) => {
                return Err(ParseDecimalError::InternalOverflow);
            }
            Ok(i) => i,
        }
    } else {
        0
    };
    if n_frac_digits > 0 {
        match checked_mul_pow_ten(coeff, n_frac_digits as u8) {
            None => return Result::Err(ParseDecimalError::InternalOverflow),
            Some(val) => coeff = val,
        }
        coeff += parts.frac_part.parse::<i128>().unwrap();
    }
    if parts.num_sign == "-" {
        Ok((-coeff, exp - n_frac_digits))
    } else {
        Ok((coeff, exp - n_frac_digits))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dec_repr_from_str;

    #[test]
    fn test_parse_int_lit() {
        let res = dec_repr_from_str("1957945").unwrap();
        assert_eq!(res, (1957945, 0));
    }

    #[test]
    fn test_parse_dec_lit() {
        let res = dec_repr_from_str("-17.5").unwrap();
        assert_eq!(res, (-175, -1));
    }

    #[test]
    fn test_parse_frac_only_lit() {
        let res = dec_repr_from_str("+.75").unwrap();
        assert_eq!(res, (75, -2));
    }

    #[test]
    fn test_parse_int_lit_neg_exp() {
        let res = dec_repr_from_str("17e-5").unwrap();
        assert_eq!(res, (17, -5));
    }

    #[test]
    fn test_parse_int_lit_pos_exp() {
        let res = dec_repr_from_str("+217e3").unwrap();
        assert_eq!(res, (217, 3));
    }

    #[test]
    fn test_parse_dec_lit_neg_exp() {
        let res = dec_repr_from_str("-533.7e-2").unwrap();
        assert_eq!(res, (-5337, -3));
    }

    #[test]
    fn test_parse_dec_lit_pos_exp() {
        let res = dec_repr_from_str("700004.002E13").unwrap();
        assert_eq!(res, (700004002, 10));
    }

    #[test]
    fn test_err_empty_str() {
        let res = dec_repr_from_str("");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::Empty);
    }

    #[test]
    fn test_err_invalid_lit() {
        let lits = [" ", "+", "-4.33.2", "2.87 e3", "+e3", ".4e3 "];
        for lit in lits {
            let res = dec_repr_from_str(lit);
            assert!(res.is_err());
            let err = res.unwrap_err();
            assert_eq!(err, ParseDecimalError::Invalid);
        }
    }

    #[test]
    fn test_frac_limit_exceeded() {
        let res =
            dec_repr_from_str("0.172958873900163775420093721180000722643");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_frac_limit_exceeded_with_exp() {
        let res = dec_repr_from_str("17.493e-36");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::FracDigitLimitExceeded);
    }

    #[test]
    fn test_int_lit_max_val_exceeded() {
        let s = "170141183460469231731687303715884105728";
        let res = dec_repr_from_str(s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::InternalOverflow);
    }

    #[test]
    fn test_dec_lit_max_val_exceeded() {
        let s = "1701411834604692317316873037158841058.00";
        let res = dec_repr_from_str(s);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(err, ParseDecimalError::InternalOverflow);
    }
}
