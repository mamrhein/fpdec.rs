use core::iter::{Product, Sum};

use crate::Decimal;

impl Sum for Decimal {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |sum, next| sum + next)
    }
}

impl Product for Decimal {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |sum, next| sum * next)
    }
}

#[cfg(test)]
mod tests {
    use fpdec_macros::Dec;

    use super::*;

    #[test]
    fn sum_iter() {
        let sum = [Dec!(1), Dec!(2), Dec!(3), Dec!(4)]
            .into_iter()
            .sum::<Decimal>();

        assert_eq!(sum, Dec!(10));
    }

    #[test]
    fn product_iter() {
        let product = [Dec!(1), Dec!(2), Dec!(3), Dec!(4)]
            .into_iter()
            .product::<Decimal>();

        assert_eq!(product, Dec!(24));
    }
}
