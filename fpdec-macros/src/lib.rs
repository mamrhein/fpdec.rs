// ---------------------------------------------------------------------------
// Copyright:   (c) 2021 ff. Michael Amrhein (michael@adrhinum.de)
// License:     This program is part of a larger application. For license
//              details please read the file LICENSE.TXT provided together
//              with the application.
// ---------------------------------------------------------------------------
// $Source$
// $Revision$

use ::proc_macro::TokenStream;

use ::quote::quote;

use fpdec_core::{dec_repr_from_str, ParseDecimalError, MAX_PRECISION};

/// Macro used to convert a number literal into a `Decimal`.
///
/// The literal must be in the form
/// \[+|-]\<int\>\[.\<frac\>]\[<e|E>\[+|-]\<exp\>] or
/// \[+|-].\<frac\>\[<e|E>\[+|-]\<exp\>].
///
/// The precision is determined by the number of fractional digits minus the
/// value of the signed exponent.
///
/// The resulting value must not exceed the limits given by the internal
/// representaion of `Decimal`:
/// * The coefficient must fit into an `i128`.
/// * The precision must not exceed the constant `MAX_PRECISION`.
///
/// # Panics
///
/// The macro panics if the conditions listed above are not met!
///
/// # Examples
///
/// ```ignore
/// let d = Dec!(17.5);
/// assert_eq!(d.to_string(), "17.5");
///
/// let d = Dec!(-170.5e-2);
/// assert_eq!(d.to_string(), "-1.705");
/// ```
#[allow(non_snake_case)]
#[proc_macro]
pub fn Dec(input: TokenStream) -> TokenStream {
    let mut src = input.to_string();
    // "-" and "+" get separated by a blank => remove it
    if src.starts_with("- ") || src.starts_with("+ ") {
        src.remove(1);
    }
    match dec_repr_from_str(&src) {
        Err(e) => panic!("{}", e),
        Ok((mut coeff, mut exponent)) => {
            if -exponent > (MAX_PRECISION as isize) {
                panic!("{}", ParseDecimalError::PrecLimitExceeded)
            }
            if exponent > 38 {
                // 10 ^ 39 > int128::MAX
                panic!("{}", ParseDecimalError::InternalOverflow);
            }
            if exponent > 0 {
                match coeff.checked_mul(10i128.pow(exponent as u32)) {
                    None => panic!("{}", ParseDecimalError::InternalOverflow),
                    Some(val) => {
                        coeff = val;
                    }
                }
                exponent = 0;
            }
            let prec = -exponent as u8;
            quote!(
                ::fpdec::Decimal::new_raw(#coeff, #prec)
            )
            .into()
        }
    }
}
