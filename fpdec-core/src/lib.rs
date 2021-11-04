// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

mod parser;
mod powers_of_ten;

use std::cmp::Ordering;

pub use parser::{dec_repr_from_str, ParseDecimalError};
pub use powers_of_ten::{checked_mul_pow_ten, mul_pow_ten, ten_pow};

/// The maximum number of fractional decimal digits supported by `Decimal`.
pub const MAX_PRECISION: u8 = 38;

#[doc(hidden)]
#[inline]
pub fn adjust_prec(x: i128, p: u8, y: i128, q: u8) -> (i128, i128) {
    match p.cmp(&q) {
        Ordering::Equal => (x, y),
        Ordering::Greater => (x, mul_pow_ten(y, p - q)),
        Ordering::Less => (mul_pow_ten(x, q - p), y),
    }
}
#[doc(hidden)]
#[inline]
pub fn checked_adjust_prec(
    x: i128,
    p: u8,
    y: i128,
    q: u8,
) -> (Option<i128>, Option<i128>) {
    match p.cmp(&q) {
        Ordering::Equal => (Some(x), Some(y)),
        Ordering::Greater => (Some(x), checked_mul_pow_ten(y, p - q)),
        Ordering::Less => (checked_mul_pow_ten(x, q - p), Some(y)),
    }
}
