// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![cfg_attr(not(feature = "std"), no_std)]

use core::cmp::Ordering;

pub use parser::{dec_repr_from_str, ParseDecimalError};
pub use powers_of_ten::{checked_mul_pow_ten, mul_pow_ten, ten_pow};

mod parser;
mod powers_of_ten;

/// The maximum number of fractional decimal digits supported by `Decimal`.
pub const MAX_N_FRAC_DIGITS: u8 = 38;

#[doc(hidden)]
#[inline]
pub fn adjust_coeffs(x: i128, p: u8, y: i128, q: u8) -> (i128, i128) {
    match p.cmp(&q) {
        Ordering::Equal => (x, y),
        Ordering::Greater => (x, mul_pow_ten(y, p - q)),
        Ordering::Less => (mul_pow_ten(x, q - p), y),
    }
}

#[doc(hidden)]
#[inline]
pub fn checked_adjust_coeffs(
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

#[doc(hidden)]
#[inline]
pub fn div_mod_floor(x: i128, y: i128) -> (i128, i128) {
    let (q, r) = (x / y, x % y);
    if (r > 0 && y < 0) || (r < 0 && y > 0) {
        (q - 1, r + y)
    } else {
        (q, r)
    }
}

#[doc(hidden)]
#[inline]
pub fn magnitude(i: i128) -> u8 {
    // TODO: change after feature(int_log) got stable:
    // i.log(10).trunc() as u8
    (i.abs() as f64).log10().trunc() as u8
}
