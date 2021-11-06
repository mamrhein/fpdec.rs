// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use fpdec::Dec;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_int_lit() {
        let d = Dec!(1957945);
        assert_eq!(d.coefficient(), 1957945);
        assert_eq!(d.precision(), 0);
    }

    #[test]
    fn test_from_dec_lit() {
        let d = Dec!(-17.5);
        assert_eq!(d.coefficient(), -175);
        assert_eq!(d.precision(), 1);
    }

    #[test]
    fn test_from_frac_only_lit() {
        let d = Dec!(+.7500);
        assert_eq!(d.coefficient(), 7500);
        assert_eq!(d.precision(), 4);
    }

    #[test]
    fn test_from_int_lit_neg_exp() {
        let d = Dec!(17e-5);
        assert_eq!(d.coefficient(), 17);
        assert_eq!(d.precision(), 5);
    }

    #[test]
    fn test_from_int_lit_pos_exp() {
        let d = Dec!(+2170e3);
        assert_eq!(d.coefficient(), 2170000);
        assert_eq!(d.precision(), 0);
    }

    #[test]
    fn test_from_dec_lit_neg_exp() {
        let d = Dec!(-533.7e-2);
        assert_eq!(d.coefficient(), -5337);
        assert_eq!(d.precision(), 3);
    }

    #[test]
    fn test_from_dec_lit_pos_exp() {
        let d = Dec!(700004.0020E13);
        assert_eq!(d.coefficient(), 7000040020000000000);
        assert_eq!(d.precision(), 0);
    }
}
