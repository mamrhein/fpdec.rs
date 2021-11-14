// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use std::ops::Add;

use num_traits::Zero;

use crate::Decimal;

impl Zero for Decimal
where
    Decimal: Add<Output = Decimal>,
{
    #[inline(always)]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.coeff.is_zero()
    }
}

#[cfg(test)]
mod zero_tests {
    use super::*;

    #[test]
    fn test_zero() {
        assert!(Decimal::is_zero(&Decimal::zero()));
        assert!(Decimal::is_zero(&Decimal::new_raw(0, 7)));
        assert!(!Decimal::is_zero(&Decimal::new_raw(1, 27)));
    }
}
