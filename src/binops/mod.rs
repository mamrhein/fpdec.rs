// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

// Implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are Decimals
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a> $imp<Decimal> for &'a Decimal
        where
            Decimal: $imp<Decimal>,
        {
            type Output = <Decimal as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: Decimal) -> Self::Output {
                $imp::$method(*self, rhs)
            }
        }
        impl $imp<&Decimal> for Decimal
        where
            Decimal: $imp<Decimal>,
        {
            type Output = <Decimal as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &Decimal) -> Self::Output {
                $imp::$method(self, *rhs)
            }
        }
        impl $imp<&Decimal> for &Decimal
        where
            Decimal: $imp<Decimal>,
        {
            type Output = <Decimal as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &Decimal) -> Self::Output {
                $imp::$method(*self, *rhs)
            }
        }
    };
}

// Same for ops giving rounded result.
macro_rules! forward_ref_binop_rounded {
    (impl $imp:ident, $method:ident) => {
        impl<'a> $imp<Decimal> for &'a Decimal
        where
            Decimal: $imp<Decimal>,
        {
            type Output = <Decimal as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: Decimal, n_frac_digits: u8) -> Decimal {
                $imp::$method(*self, rhs, n_frac_digits)
            }
        }
        impl $imp<&Decimal> for Decimal
        where
            Decimal: $imp<Decimal>,
        {
            type Output = <Decimal as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &Decimal, n_frac_digits: u8) -> Decimal {
                $imp::$method(self, *rhs, n_frac_digits)
            }
        }
        impl $imp<&Decimal> for &Decimal
        where
            Decimal: $imp<Decimal>,
        {
            type Output = <Decimal as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &Decimal, n_frac_digits: u8) -> Decimal {
                $imp::$method(*self, *rhs, n_frac_digits)
            }
        }
    };
}

// Implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T = Decimal and U is a native int
macro_rules! forward_ref_binop_decimal_int {
    (impl $imp:ident, $method:ident) => {
        forward_ref_binop_decimal_int!(
            impl $imp, $method, u8, i8, u16, i16, u32, i32, u64, i64, i128
        );
    };
    (impl $imp:ident, $method:ident, $($t:ty),*) => {
        $(
        impl<'a> $imp<$t> for &'a Decimal
        where
            Decimal: $imp<$t>,
        {
            type Output = <Decimal as $imp<$t>>::Output;

            #[inline(always)]
            fn $method(self, rhs: $t) -> Self::Output {
                $imp::$method(*self, rhs)
            }
        }
        impl $imp<&$t> for Decimal
        where
            Decimal: $imp<$t>,
        {
            type Output = <Decimal as $imp<$t>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &$t) -> Self::Output {
                $imp::$method(self, *rhs)
            }
        }
        impl $imp<&$t> for &Decimal
        where
            Decimal: $imp<$t>,
        {
            type Output = <Decimal as $imp<$t>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &$t) -> Self::Output {
                $imp::$method(*self, *rhs)
            }
        }
        impl<'a> $imp<Decimal> for &'a $t
        where
            $t: $imp<Decimal>,
        {
            type Output = <$t as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: Decimal) -> Self::Output {
                $imp::$method(*self, rhs)
            }
        }
        impl $imp<&Decimal> for $t
        where
            $t: $imp<Decimal>,
        {
            type Output = <$t as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &Decimal) -> Self::Output {
                $imp::$method(self, *rhs)
            }
        }
        impl $imp<&Decimal> for &$t
        where
            $t: $imp<Decimal>,
        {
            type Output = <$t as $imp<Decimal>>::Output;

            #[inline(always)]
            fn $method(self, rhs: &Decimal) -> Self::Output {
                $imp::$method(*self, *rhs)
            }
        }
        )*
    }
}

macro_rules! forward_op_assign {
    (impl $imp:ident, $method:ident, $base_imp:ident, $base_method:ident) => {
        impl<T> $imp<T> for Decimal
        where
            Decimal: $base_imp<T, Output = Self>,
        {
            #[inline(always)]
            fn $method(&mut self, rhs: T) {
                *self = $base_imp::$base_method(*self, rhs);
            }
        }
    };
}

mod add_sub;
pub(crate) mod checked_add_sub;
pub(crate) mod checked_div;
pub(crate) mod checked_mul;
pub(crate) mod checked_rem;
mod cmp;
pub(crate) mod div;
pub(crate) mod div_rounded;
mod mul;
pub(crate) mod mul_rounded;
mod rem;
