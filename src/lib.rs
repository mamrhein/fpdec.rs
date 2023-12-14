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
#![allow(dead_code)]
// activate some clippy lints
#![warn(clippy::cast_possible_truncation)]
#![warn(clippy::cast_precision_loss)]
#![warn(clippy::cognitive_complexity)]
#![warn(clippy::decimal_literal_representation)]
#![warn(clippy::enum_glob_use)]
#![warn(clippy::equatable_if_let)]
#![warn(clippy::fallible_impl_from)]
#![warn(clippy::if_not_else)]
#![warn(clippy::if_then_some_else_none)]
#![warn(clippy::implicit_clone)]
#![warn(clippy::integer_division)]
#![warn(clippy::manual_assert)]
#![warn(clippy::match_same_arms)]
#![warn(clippy::mismatching_type_param_order)]
#![warn(clippy::missing_const_for_fn)]
#![warn(clippy::missing_errors_doc)]
#![warn(clippy::missing_panics_doc)]
#![warn(clippy::multiple_crate_versions)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::needless_pass_by_value)]
#![warn(clippy::print_stderr)]
#![warn(clippy::print_stdout)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::unicode_not_nfc)]
#![warn(clippy::unimplemented)]
#![warn(clippy::unseparated_literal_suffix)]
#![warn(clippy::unused_self)]
#![warn(clippy::unwrap_in_result)]
#![warn(clippy::use_self)]
#![warn(clippy::used_underscore_binding)]
#![warn(clippy::wildcard_imports)]

extern crate alloc;

#[cfg(feature = "serde-as-str")]
use alloc::string::String;
use core::hash::{Hash, Hasher};

#[doc(inline)]
pub use as_integer_ratio::AsIntegerRatio;
#[doc(inline)]
pub use binops::{
    checked_add_sub::CheckedAdd, checked_add_sub::CheckedSub,
    checked_div::CheckedDiv, checked_mul::CheckedMul,
    checked_rem::CheckedRem, div_rounded::DivRounded,
    mul_rounded::MulRounded,
};
#[doc(inline)]
pub use errors::*;
use fpdec_core::i128_magnitude;
#[doc(inline)]
pub use fpdec_core::{
    ParseDecimalError, Round, RoundingMode, MAX_N_FRAC_DIGITS,
};
#[doc(inline)]
pub use fpdec_macros::Dec;
#[doc(inline)]
pub use quantize::Quantize;

mod as_integer_ratio;
mod binops;
mod errors;
mod format;
mod from_float;
mod from_int;
mod from_str;
mod into_float;
mod into_int;
#[cfg(feature = "num-traits")]
mod num_traits;
mod quantize;
mod round;
mod unops;

/// Represents a decimal number as a coefficient (`i128`) combined with a
/// value (`u8`) specifying the number of fractional decimal digits.
///
/// The number of fractional digits can be in the range 0 ..
/// [`MAX_N_FRAC_DIGITS`].
#[must_use]
#[derive(Copy, Clone)]
#[cfg_attr(
    feature = "serde-as-str",
    derive(serde::Serialize, serde::Deserialize),
    serde(into = "String"),
    serde(try_from = "String")
)]
// Derived `Archive` implementation doesn't support packed structs.
// More details: https://github.com/rkyv/rkyv/issues/198
//
// To overcome this, we use a manually written implementation for
// cases when both `rkyv` and `packed` features are enabled.
#[cfg_attr(
    all(feature = "rkyv", not(feature = "packed")),
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize),
    archive(check_bytes),
    archive_attr(derive(Copy, Clone))
)]
#[cfg_attr(feature = "packed", repr(packed))]
pub struct Decimal {
    coeff: i128,
    n_frac_digits: u8,
}

impl Decimal {
    // needs to be public because of macro Dec!
    #[doc(hidden)]
    #[inline(always)]
    pub const fn new_raw(coeff: i128, n_frac_digits: u8) -> Self {
        debug_assert!(
            n_frac_digits <= MAX_N_FRAC_DIGITS,
            "More than MAX_N_FRAC_DIGITS fractional decimal digits \
             requested."
        );
        Self {
            coeff,
            n_frac_digits,
        }
    }

    /// Coefficient of `self`.
    #[must_use]
    #[inline(always)]
    pub const fn coefficient(self) -> i128 {
        self.coeff
    }

    /// Number of fractional decimal digits of `self`.
    #[must_use]
    #[inline(always)]
    pub const fn n_frac_digits(self) -> u8 {
        self.n_frac_digits
    }

    /// Returns the positional index of the most significant decimal digit of
    /// `self`.
    ///
    /// Special case: for a value equal to 0 `magnitude()` returns 0.
    ///
    /// # Examples:
    ///
    /// ```rust
    /// # use fpdec::{Dec, Decimal};
    /// let d = Dec!(123);
    /// assert_eq!(d.magnitude(), 2);
    /// let d = Dec!(0.00123);
    /// assert_eq!(d.magnitude(), -3);
    /// let d = Decimal::ZERO;
    /// assert_eq!(d.magnitude(), 0);
    #[must_use]
    #[inline(always)]
    pub const fn magnitude(self) -> i8 {
        i128_magnitude(self.coeff) as i8 - self.n_frac_digits as i8
    }

    /// Additive identity
    pub const ZERO: Self = Self {
        coeff: 0,
        n_frac_digits: 0,
    };

    /// Multiplicative identity
    pub const ONE: Self = Self {
        coeff: 1,
        n_frac_digits: 0,
    };

    /// Multiplicative negator
    pub const NEG_ONE: Self = Self {
        coeff: -1,
        n_frac_digits: 0,
    };

    /// Equivalent of 2
    pub const TWO: Self = Self {
        coeff: 2,
        n_frac_digits: 0,
    };

    /// Equivalent of 10
    pub const TEN: Self = Self {
        coeff: 10,
        n_frac_digits: 0,
    };

    /// Maximum value representable by `Decimal` = 2¹²⁷ - 1
    pub const MAX: Self = Self {
        coeff: i128::MAX,
        n_frac_digits: 0,
    };

    /// Minimum value representable by `Decimal`  = -2¹²⁷ + 1
    pub const MIN: Self = Self {
        coeff: i128::MIN + 1,
        n_frac_digits: 0,
    };

    /// Smallest absolute difference between two non-equal values of `Decimal`
    pub const DELTA: Self = Self {
        coeff: 1_i128,
        n_frac_digits: MAX_N_FRAC_DIGITS,
    };
}

#[inline]
pub(crate) fn normalize(coeff: &mut i128, n_frac_digits: &mut u8) {
    if *coeff == 0 {
        *n_frac_digits = 0;
    } else {
        // eliminate trailing zeros in coeff
        while *coeff % 10 == 0 && *n_frac_digits > 0 {
            *coeff /= 10;
            *n_frac_digits -= 1;
        }
    }
}

impl Default for Decimal {
    /// Default value: Decimal::ZERO
    #[inline(always)]
    fn default() -> Self {
        Self::ZERO
    }
}

impl Hash for Decimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_integer_ratio().hash(state);
    }
}

// Since core::hash::SipHasher is deprecated there is no 'default hasher' in
// core
#[cfg(feature = "std")]
#[cfg(test)]
mod hash_tests {
    use std::collections::hash_map::DefaultHasher;

    use super::*;

    fn hash<T: Hash>(t: &T) -> u64 {
        let mut h = DefaultHasher::new();
        t.hash(&mut h);
        h.finish()
    }

    #[test]
    fn test_hash_equiv_values() {
        assert_eq!(hash(&Dec!(3.4)), hash(&Dec!(3.400)));
    }

    #[test]
    fn test_hash_equiv_ratio() {
        let d = Dec!(338.5148);
        let r = d.as_integer_ratio();
        assert_eq!(hash(&d), hash(&r));
    }
}

#[cfg(feature = "serde-as-str")]
#[cfg(test)]
mod serde_json_tests {
    use serde_json;

    use super::*;

    #[test]
    fn test_min() {
        let d = Decimal::MIN;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_neg_one() {
        let d = Decimal::NEG_ONE;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_zero() {
        let d = Decimal::ZERO;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_delta() {
        let d = Decimal::DELTA;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_some() {
        let d = Dec!(123456789012345678.90123);
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }

    #[test]
    fn test_max() {
        let d = Decimal::MAX;
        let s = serde_json::to_value(d).unwrap();
        assert_eq!(d, serde_json::from_value::<Decimal>(s).unwrap());
    }
}

#[cfg(feature = "rkyv")]
impl ArchivedDecimal {
    /// Coefficient of `self`.
    #[must_use]
    #[inline(always)]
    pub const fn coefficient(self) -> i128 {
        self.coeff
    }

    /// Number of fractional decimal digits of `self`.
    #[must_use]
    #[inline(always)]
    pub const fn n_frac_digits(self) -> u8 {
        self.n_frac_digits
    }
}

/// Represents an archived decimal number.
///
/// It is a mirror of `Decimal` used in conjunction with `rkyv` and
/// `packed` features, accompanied with a manual `rkyv::Archive`
/// implementation.
#[cfg(all(feature = "rkyv", feature = "packed"))]
#[derive(Copy, Clone)]
#[repr(C, packed)]
pub struct ArchivedDecimal {
    coeff: i128,
    n_frac_digits: u8,
}

#[cfg(all(feature = "rkyv", feature = "packed"))]
impl rkyv::Archive for Decimal {
    type Archived = ArchivedDecimal;
    type Resolver = ();

    // Safety: Rkyv provides a valid pointer. Writes are unaligned,
    // which is a safe way to write the values as our type is packed.
    #[allow(unsafe_code)]
    unsafe fn resolve(
        &self,
        _: usize,
        _: Self::Resolver,
        out: *mut Self::Archived,
    ) {
        core::ptr::addr_of_mut!((*out).coeff).write_unaligned(self.coeff);
        core::ptr::addr_of_mut!((*out).n_frac_digits)
            .write_unaligned(self.n_frac_digits);
    }
}

#[cfg(all(feature = "rkyv", feature = "packed"))]
impl<S: rkyv::Fallible + ?Sized> rkyv::Serialize<S> for Decimal {
    fn serialize(&self, _: &mut S) -> Result<Self::Resolver, S::Error> {
        Ok(())
    }
}

#[cfg(all(feature = "rkyv", feature = "packed"))]
impl<D: rkyv::Fallible + ?Sized> rkyv::Deserialize<Decimal, D>
    for ArchivedDecimal
{
    fn deserialize(&self, _: &mut D) -> Result<Decimal, D::Error> {
        Ok(Decimal {
            coeff: self.coeff,
            n_frac_digits: self.n_frac_digits,
        })
    }
}

#[cfg(all(feature = "rkyv", feature = "packed"))]
impl<C: ?Sized> rkyv::CheckBytes<C> for ArchivedDecimal {
    type Error = rkyv::bytecheck::StructCheckError;

    // Safety: Rkyv provides a valid pointer.
    #[allow(unsafe_code)]
    #[inline]
    unsafe fn check_bytes<'a>(
        value: *const Self,
        context: &mut C,
    ) -> Result<&'a Self, Self::Error> {
        i128::check_bytes(core::ptr::addr_of!((*value).coeff), context)
            .map_err(|error| Self::Error {
                field_name: "coeff",
                inner: alloc::boxed::Box::new(error),
            })?;
        u8::check_bytes(core::ptr::addr_of!((*value).n_frac_digits), context)
            .map_err(|error| Self::Error {
                field_name: "n_frac_digits",
                inner: alloc::boxed::Box::new(error),
            })?;
        Ok(&*value)
    }
}

#[cfg(feature = "rkyv")]
#[cfg(test)]
mod rkyv_tests {
    use rkyv::{self, Deserialize};

    use super::*;

    fn roundtrip(value: Decimal) -> Decimal {
        let bytes = rkyv::to_bytes::<_, 256>(&value)
            .expect("Scratch space size is not enough to serialize value");
        let archived =
            rkyv::check_archived_root::<Decimal>(&bytes[..]).unwrap();
        archived
            .deserialize(&mut rkyv::Infallible)
            .expect("Deserialization is infallible")
    }

    #[test]
    fn test_roundtrip_min() {
        let d = Decimal::MIN;
        let u = roundtrip(d);
        assert_eq!(d, u);
    }

    #[test]
    fn test_min() {
        let d = Decimal::MIN;
        let u = roundtrip(d);
        assert_eq!(d, u);
    }

    #[test]
    fn test_neg_one() {
        let d = Decimal::NEG_ONE;
        let u = roundtrip(d);
        assert_eq!(d, u);
    }

    #[test]
    fn test_zero() {
        let d = Decimal::ZERO;
        let u = roundtrip(d);
        assert_eq!(d, u);
    }

    #[test]
    fn test_delta() {
        let d = Decimal::DELTA;
        let u = roundtrip(d);
        assert_eq!(d, u);
    }

    #[test]
    fn test_some() {
        let d = Dec!(123456789012345678.90123);
        let u = roundtrip(d);
        assert_eq!(d, u);
    }

    #[test]
    fn test_max() {
        let d = Decimal::MAX;
        let u = roundtrip(d);
        assert_eq!(d, u);
    }
}
