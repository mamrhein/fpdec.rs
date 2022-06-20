// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

#![doc = include_str ! ("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
// activate some rustc lints
#![deny(non_ascii_idents)]
#![deny(unsafe_code)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused)]

use core::{cmp::Ordering, ops::Neg};

pub use parser::{dec_repr_from_str, ParseDecimalError};
pub use powers_of_ten::{checked_mul_pow_ten, mul_pow_ten, ten_pow};
pub use rounding::{
    i128_div_rounded, i128_mul_div_ten_pow_rounded, i128_shifted_div_rounded,
    Round, RoundingMode,
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
pub fn i128_div_mod_floor(x: i128, y: i128) -> (i128, i128) {
    let (q, r) = (x / y, x % y);
    if (r > 0 && y < 0) || (r < 0 && y > 0) {
        (q - 1, r + y)
    } else {
        (q, r)
    }
}

// The following code is a partial copy of rust core int_log10.rs
// TODO: remove after feature(int_log) got stable

// 0 < val <= u8::MAX
#[inline]
pub const fn u8(val: u8) -> u32 {
    let val = val as u32;

    // For better performance, avoid branches by assembling the solution
    // in the bits above the low 8 bits.

    // Adding c1 to val gives 10 in the top bits for val < 10, 11 for val >= 10
    const C1: u32 = 0b11_00000000 - 10; // 758
                                        // Adding c2 to val gives 01 in the top bits for val < 100, 10 for val >=
                                        // 100
    const C2: u32 = 0b10_00000000 - 100; // 412

    // Value of top bits:
    //            +c1  +c2  1&2
    //     0..=9   10   01   00 = 0
    //   10..=99   11   01   01 = 1
    // 100..=255   11   10   10 = 2
    ((val + C1) & (val + C2)) >> 8
}

// 0 < val < 100_000
#[inline]
const fn less_than_5(val: u32) -> u32 {
    // Similar to u8, when adding one of these constants to val,
    // we get two possible bit patterns above the low 17 bits,
    // depending on whether val is below or above the threshold.
    const C1: u32 = 0b011_00000000000000000 - 10; // 393206
    const C2: u32 = 0b100_00000000000000000 - 100; // 524188
    const C3: u32 = 0b111_00000000000000000 - 1000; // 916504
    const C4: u32 = 0b100_00000000000000000 - 10000; // 514288

    // Value of top bits:
    //                +c1  +c2  1&2  +c3  +c4  3&4   ^
    //         0..=9  010  011  010  110  011  010  000 = 0
    //       10..=99  011  011  011  110  011  010  001 = 1
    //     100..=999  011  100  000  110  011  010  010 = 2
    //   1000..=9999  011  100  000  111  011  011  011 = 3
    // 10000..=99999  011  100  000  111  100  100  100 = 4
    (((val + C1) & (val + C2)) ^ ((val + C3) & (val + C4))) >> 17
}

// 0 < val <= u16::MAX
#[inline]
pub const fn u16(val: u16) -> u32 {
    less_than_5(val as u32)
}

// 0 < val <= u32::MAX
#[inline]
pub const fn u32(mut val: u32) -> u32 {
    let mut log = 0;
    if val >= 100_000 {
        val /= 100_000;
        log += 5;
    }
    log + less_than_5(val)
}

// 0 < val <= u64::MAX
#[inline]
pub const fn u64(mut val: u64) -> u32 {
    let mut log = 0;
    if val >= 10_000_000_000 {
        val /= 10_000_000_000;
        log += 10;
    }
    if val >= 100_000 {
        val /= 100_000;
        log += 5;
    }
    log + less_than_5(val as u32)
}

// 0 < val <= u128::MAX
#[inline]
pub const fn u128(mut val: u128) -> u32 {
    let mut log = 0;
    if val >= 100_000_000_000_000_000_000_000_000_000_000 {
        val /= 100_000_000_000_000_000_000_000_000_000_000;
        log += 32;
        return log + u32(val as u32);
    }
    if val >= 10_000_000_000_000_000 {
        val /= 10_000_000_000_000_000;
        log += 16;
    }
    log + u64(val as u64)
}

// --- end of copied code ---

#[doc(hidden)]
#[inline]
pub const fn i128_magnitude(i: i128) -> u8 {
    // TODO: change after feature(int_log) got stable:
    // i.log10() as u8
    u128(i.abs() as u128) as u8
}

/// Return the index of the most significant bit of an u128.
/// The given u128 must not be zero!
fn u128_msb(mut i: u128) -> u8 {
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

#[inline(always)]
fn u128_hi(u: u128) -> u128 {
    u >> 64
}

#[inline(always)]
fn u128_lo(u: u128) -> u128 {
    u & 0xffffffffffffffff
}

#[inline(always)]
fn u128_mul_u128(x: u128, y: u128) -> (u128, u128) {
    let xh = u128_hi(x);
    let xl = u128_lo(x);
    let yh = u128_hi(y);
    let yl = u128_lo(y);
    let mut t = xl * yl;
    let mut rl = u128_lo(t);
    t = xl * yh + u128_hi(t);
    let mut rh = u128_hi(t);
    t = xh * yl + u128_lo(t);
    rl += u128_lo(t) << 64;
    rh += xh * yh + u128_hi(t);
    (rh, rl)
}

// Calculate x = x / y in place, where x = xh * 2^128 + xl, and return x % y.
// Adapted from
// D. E. Knuth, The Art of Computer Programming, Vol. 2, Ch. 4.3.1,
// Exercise 16
#[inline(always)]
fn u256_idiv_u64(xh: &mut u128, xl: &mut u128, y: u64) -> u128 {
    if y == 1 {
        return 0;
    }
    let y = y as u128;
    let mut th = u128_hi(*xh);
    let mut r = th % y;
    let mut tl = (r << 64) + u128_lo(*xh);
    *xh = ((th / y) << 64) + tl / y;
    r = tl % y;
    th = (r << 64) + u128_hi(*xl);
    r = th % y;
    tl = (r << 64) + u128_lo(*xl);
    *xl = ((th / y) << 64) + tl / y;
    tl % y
}

// Calculate x = x / y in place, where x = xh * 2^128 + xl, and return x % y.
// Specialized version adapted from
// Henry S. Warren, Hacker’s Delight,
// originally found at http://www.hackersdelight.org/HDcode/divlu.c.txt.
// That code is in turn based on Algorithm D from
// D. E. Knuth, The Art of Computer Programming, Vol. 2, Ch. 4.3.1,
// adapted to the special case m = 4 and n = 2 and xh < y (!).
// The link given above does not exist anymore, but the code can still be
// found at https://github.com/hcs0/Hackers-Delight/blob/master/divlu.c.txt.
#[inline(always)]
fn u256_idiv_u128_special(xh: &mut u128, xl: &mut u128, mut y: u128) -> u128 {
    debug_assert!(*xh < y);
    const B: u128 = 1 << 64;
    // Normalize dividend and divisor, so that y > 2^127 (i.e. highest bit set)
    let n_bits = 127 - u128_msb(y);
    y <<= n_bits;
    let yn1 = u128_hi(y);
    let yn0 = u128_lo(y);
    // bits to be shifted from xl to xh:
    let sh = if n_bits == 0 {
        0
    } else {
        *xl >> (128 - n_bits)
    };
    let xn32 = *xh << n_bits | sh;
    let xn10 = *xl << n_bits;
    let xn1 = u128_hi(xn10);
    let xn0 = u128_lo(xn10);
    let mut q1 = xn32 / yn1;
    let mut rhat = xn32 % yn1;
    // Now we have
    // q1 * yn1 + rhat = xn32
    // so that
    // q1 * yn1 * 2^64 + rhat * 2^64 + xn1 = xn32 * 2^64 + xn1
    while q1 >= B || q1 * yn0 > rhat * B + xn1 {
        q1 -= 1;
        rhat += yn1;
        if rhat >= B {
            break;
        }
    }
    // The loop did not change the equation given above. It was terminated if
    // either q1 < 2^64 or rhat >= 2^64 or q1 * yn0 > rhat * 2^64 + xn1.
    // In these cases follows:
    // q1 * yn0 <= rhat * 2^64 + xn1, therefor
    // q1 * yn1 * 2^64 + q1 * yn0 <= xn32 * 2^64 + xn1, and
    // q1 * y <= xn32 * 2^64 + xn1, and
    // xn32 * 2^64 + xn1 - q1 * y >= 0.
    // That means that the add-back step in Knuth's algorithm is not required.

    // Since the final quotient is < 2^128, this must also be true for
    // xn32 * 2^64 + xn1 - q1 * y. Thus, in the following we can safely
    // ignore any possible overflow in xn32 * 2^64 or q1 * y.
    let t = xn32
        .wrapping_mul(B)
        .wrapping_add(xn1)
        .wrapping_sub(q1.wrapping_mul(y));
    let mut q0 = t / yn1;
    rhat = t % yn1;
    while q0 >= B || q0 * yn0 > rhat * B + xn0 {
        q0 -= 1;
        rhat += yn1;
        if rhat >= B {
            break;
        }
    }
    // Write back result
    *xh = 0;
    *xl = q1 * B + q0;
    // Denormalize remainder
    (t.wrapping_mul(B)
        .wrapping_add(xn0)
        .wrapping_sub(q0.wrapping_mul(y)))
        >> n_bits
}

// Calculate x = x / y in place, where x = xh * 2^128 + xl, and return x % y.
#[inline(always)]
fn u256_idiv_u128(xh: &mut u128, xl: &mut u128, y: u128) -> u128 {
    if u128_hi(y) == 0 {
        return u256_idiv_u64(xh, xl, u128_lo(y) as u64);
    }
    if *xh < y {
        return u256_idiv_u128_special(xh, xl, y);
    }
    let mut t = *xh % y;
    let r = u256_idiv_u128_special(&mut t, xl, y);
    *xh /= y;
    r
}

/// Return `Some<(q, r)>` with `q = (x * 10^p) / y` and `r = (x * 10^p) % y`,
/// so that `(x * 10^p) = q * y + r`, where q is rounded against floor so that
/// r, if non-zero, has the same sign as y and `0 <= abs(r) < abs(y)`, or return
/// `None` if |q| > i128::MAX.
#[doc(hidden)]
pub fn i128_shifted_div_mod_floor(
    x: i128,
    p: u8,
    y: i128,
) -> Option<(i128, i128)> {
    let (mut xh, mut xl) = u128_mul_u128(x.unsigned_abs(), ten_pow(p) as u128);
    let r = u256_idiv_u128(&mut xh, &mut xl, y.unsigned_abs());
    if xh != 0 || xl > i128::MAX as u128 {
        return None;
    }
    // xl <= i128::MAX, so xl as i128 is safe.
    let mut q = xl as i128;
    // r < y, so r as i128 is safe.
    let mut r = r as i128;
    if x.is_negative() {
        if y.is_negative() {
            r = r.neg();
        } else {
            q = q.neg() - 1;
            r = y - r;
        }
    } else if y.is_negative() {
        q = q.neg() - 1;
        r -= y;
    }
    Some((q, r))
}

/// Return `Some<(q, r)>` with `q = (x1 * x2) / y` and `r = (x1 * x2) % y`,
/// so that `(x1 * x2) = q * y + r`, where q is rounded against floor so that
/// r, if non-zero, has the same sign as y and `0 <= abs(r) < abs(y)`, or return
/// `None` if |q| > i128::MAX.
#[doc(hidden)]
pub fn i256_div_mod_floor(x1: i128, x2: i128, y: i128) -> Option<(i128, i128)> {
    debug_assert!(y > 0);
    let (mut xh, mut xl) = u128_mul_u128(x1.unsigned_abs(), x2.unsigned_abs());
    let r = u256_idiv_u128(&mut xh, &mut xl, y.unsigned_abs());
    if xh != 0 || xl > i128::MAX as u128 {
        return None;
    }
    // xl <= i128::MAX, so xl as i128 is safe.
    let mut q = xl as i128;
    // r < y, so r as i128 is safe.
    let mut r = r as i128;
    if x1.is_negative() != x2.is_negative() {
        q = q.neg() - 1;
        r = y - r;
    }
    Some((q, r))
}
