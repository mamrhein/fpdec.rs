This crate provides a fast implementation of `Decimal` fixed-point 
arithmetics.
It is targeted at typical business applications, dealing with numbers 
representing quantities, money and the like, not at scientific computations,
for which the accuracy of floating point math is - in most cases - sufficient.
### Objectives
* "Exact" representation of decimal numbers (no deviation as with binary
  floating point numbers)
* No hidden rounding errors (as inherent to floating point math)
* Very fast operations (by mapping them to integer ops) 
* Range of representable decimal numbers sufficient for typical business
  applications

At the binary level a `Decimal` number is represented as a coefficient (stored 
as an `i128` value) combined with a value specifying the number of fractional 
decimal digits (stored as a `u8`). The latter is limited to a value given by 
the constant `MAX_N_FRAC_DIGITS` = 38.

### Status
Experimental (work in progess)

## Getting started

Add `fpdec` to your `Cargo.toml`:

```toml
[dependencies]
fpdec = "0.3"
```

## Usage

A `Decimal` number can be created in different ways. 

The easiest method is to use the procedural macro `Dec`:

```rust
# use fpdec::{Dec, Decimal};
let d = Dec!(-17.5);
assert_eq!(d.to_string(), "-17.5");
```

Alternatively you can convert an integer, a float or a string to a `Decimal`:

```rust
# use fpdec::Decimal;
let d = Decimal::from(297_i32);
assert_eq!(d.to_string(), "297");
```

```rust
# use fpdec::{Decimal, DecimalError};
# use std::convert::TryFrom;
let d = Decimal::try_from(83.25_f64)?;
assert_eq!(d.to_string(), "83.25");
# Ok::<(), DecimalError>(())
```

```rust
# use fpdec::{Decimal, ParseDecimalError};
# use std::str::FromStr;
let d = Decimal::from_str("38.2070")?;
assert_eq!(d.to_string(), "38.2070");
# Ok::<(), ParseDecimalError>(())
```

The sign of a `Decimal` can be inverted using the unary minus operator and a
`Decimal` instance can be compared to other instances of type `Decimal` or all
basic types of integers (besides u128):

```rust
# use fpdec::{Dec, Decimal};
let x = Dec!(129.24);
let y = -x;
assert_eq!(y.to_string(), "-129.24");
assert!(-129_i64 > y);
let z = -y;
assert_eq!(x, z);
let z = Dec!(0.00097);
assert!(x > z);
assert!(y <= z);
assert!(z != 7_u32);
assert!(7_u32 == Dec!(7.00));
```

`Decimal` supports all five binary numerical operators +, -, *, /, and %, with
two `Decimal`s or with a `Decimal` and a basic integer (besides u128):

```rust
# use fpdec::{Dec, Decimal};
let x = Dec!(17.5);
let y = Dec!(6.40);
let z = x + y;
assert_eq!(z.to_string(), "23.90");
let z = x - y;
assert_eq!(z.to_string(), "11.10");
let z = x * y;
assert_eq!(z.to_string(), "112.000");
let z = x / y;
assert_eq!(z.to_string(), "2.734375");
let z = x % y;
assert_eq!(z.to_string(), "4.70");
```

```rust
# use fpdec::{Dec, Decimal};
let x = Dec!(17.5);
let y = -5_i64;
let z = x + y;
assert_eq!(z.to_string(), "12.5");
let z = x - y;
assert_eq!(z.to_string(), "22.5");
let z = y * x;
assert_eq!(z.to_string(), "-87.5");
let z = x / y;
assert_eq!(z.to_string(), "-3.5");
let z = x % y;
assert_eq!(z.to_string(), "2.5");
```

All these binary numeric operators panic if the result is not representable as 
a `Decimal` according to the constraints stated above. In addition, there are
functions implementing "checked" variants of the operators which return
`Option::None` instead of panicking.

For Multiplication and Division there are also functions which return a result
rounded to a given number of fractional digits:

```rust
# use fpdec::{Dec, Decimal, DivRounded, MulRounded};
let x = Dec!(17.5);
let y = Dec!(6.47);
let z: Decimal = x.mul_rounded(y, 1);
assert_eq!(z.to_string(), "113.2");
let z: Decimal = x.div_rounded(y, 3);
assert_eq!(z.to_string(), "2.705");
```
