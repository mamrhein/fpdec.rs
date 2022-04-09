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
use std::cmp::min;
use std::ops::Neg;

pub use parser::{dec_repr_from_str, ParseDecimalError};
pub use powers_of_ten::{checked_mul_pow_ten, mul_pow_ten, ten_pow};
pub use rounding::{
    div_i128_rounded, div_shifted_i128_rounded, Round, RoundingMode,
};

mod parser;
mod powers_of_ten;
mod rounding;

/// The maximum number of fractional decimal digits supported by `Decimal`.
pub const MAX_N_FRAC_DIGITS: u8 = 18;

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

/// Return `(q, r)` with `q = x / y` and `r = x % y`, so that `x = q * y + r`,
/// where q is rounded against floor so that r, if non-zero, has the same sign
/// as y and `0 <= abs(r) < abs(y)`.
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

/// Return the index of the most significant bit of an u128.
/// The given u128 must not be zero!
fn msb(mut i: u128) -> u8 {
    debug_assert_ne!(i, 0);
    const IDX_MAP: [u8; 16] = [0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4];
    let mut n: u8 = 0;
    if i & 0xffffffffffffffff0000000000000000_u128 != 0 {
        n = 64;
        i >>= 64;
    };
    if i & 0x0000000000000000ffffffff00000000_u128 != 0 {
        n += 32;
        i >>= 32;
    };
    if i & 0x000000000000000000000000ffff0000_u128 != 0 {
        n += 16;
        i >>= 16;
    };
    if i & 0x0000000000000000000000000000ff00_u128 != 0 {
        n += 8;
        i >>= 8;
    };
    if i & 0x000000000000000000000000000000f0_u128 != 0 {
        n += 4;
        i >>= 4;
    };
    n + IDX_MAP[i as usize] - 1
}

/// Return `(q, r)` with `q = (x * 10^p) / y` and `r = (x * 10^p) % y`, so that
/// `(x * 10^p) = q * y + r`, where q is rounded against floor so that r, if
/// non-zero, has the same sign as y and `0 <= abs(r) < abs(y)`.
#[doc(hidden)]
pub fn shifted_div_mod_floor(x: i128, p: u8, y: i128) -> Option<(i128, i128)> {
    // x * 10^p may overflow, so we proceed stepwise, in each step shifting the
    // divident so that it highest bit is set.
    let mut q: u128 = 0;
    let mut r = x.abs() as u128;
    let d = y.abs() as u128;
    let neg = x.is_negative() != y.is_negative();
    let mut n = p;
    while n > 0 {
        let m = min(n, 127_u8 - msb(r));
        q = q.checked_shl(m as u32)?;
        let t = r << m;
        q = q.checked_add(t / d)?;
        r = t % d;
        n -= m;
    }
    let sh = 5_u128.pow(p as u32);
    q = q.checked_mul(sh as u128)?;
    let t = r.checked_mul(sh as u128)?;
    if q > (1 << 127) - 1 {
        return None;
    }
    let (mut sq, sr) = div_mod_floor(t as i128, y);
    sq += q as i128;
    if neg {
        sq = sq.neg();
    }
    Some((sq, sr))
}
