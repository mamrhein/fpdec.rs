This crate provides a fast implementation of `Decimal` floating-point 
arithmetics.
It is targeted at typical business applications, dealing with numbers 
representing quantities, money and the like, not at scientific computations,
for which the accuracy of binary floating point math is - in most cases -
sufficient.
### Objectives
* "Exact" representation of decimal numbers (no deviation as with binary
  floating point numbers)
* No hidden rounding errors (as inherent to binary floating point math)
* Very fast operations (by mapping them to integer ops) 
* Range of representable decimal numbers sufficient for typical business
  applications

At the binary level a `Decimal` number is represented as a coefficient (stored 
as an `i128` value) combined with a value specifying the number of fractional 
decimal digits (stored as a `u8`). The latter is limited to a value given by 
the constant `MAX_N_FRAC_DIGITS` = 18.

### Status
Work in progess, but most of the API is stable.

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
# use core::convert::TryFrom;
let d = Decimal::try_from(83.25_f64)?;
assert_eq!(d.to_string(), "83.25");
# Ok::<(), DecimalError>(())
```

```rust
# use fpdec::{Decimal, ParseDecimalError};
# use core::str::FromStr;
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
The results of Multiplication or Division are not exact in any case. If the
number of fractional decimal digits of the exact result would exceed
`MAX_N_FRAC_DIGITS` fractional decimal digits, the result given is rounded to
fit this limit.

```rust
# use fpdec::{Dec, Decimal};
let x = Dec!(1e-10);
let y = Dec!(75e-9);
let z = x * y;
assert_eq!(z.to_string(), "0.000000000000000008");
let x = Dec!(1.);
let y = Dec!(3.);
let z = x / y;
assert_eq!(z.to_string(), "0.333333333333333333");
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

A `Decimal` value can be converted into a float, maybe rounded to the nearest 
value representable by the target type:

```rust
# use fpdec::{Dec, Decimal};
let d = Dec!(-33820900478.195);
let f = f64::from(d);
assert_eq!(f, -33820900478.19499969482421875_f64);
let f = f32::from(Dec!(0.6));
assert_eq!(f, 0.60000002384185791015625_f32);
```

Converting a `Decimal` value to a primitive int is more intricate. It is only 
supported by try_from / try_into and only giving a value of the target type,
if the given value represents an integral value fitting the range of values of
the target type.

```rust
# use fpdec::{Dec, Decimal, TryFromDecimalError};
let d = Dec!(3.7);
let res = i32::try_from(d);
assert!(res.is_err());
assert_eq!(res.unwrap_err(), TryFromDecimalError::NotAnIntValue);
let d = Decimal::MAX;
let res = i128::try_from(d);
assert_eq!(res.unwrap(), i128::MAX);
let res = i64::try_from(d);
assert!(res.is_err());
assert_eq!(res.unwrap_err(), TryFromDecimalError::ValueOutOfRange);
```
## Crate features

By default, only the feature `std` is enabled.

### Ecosystem

* **std** - When enabled, this will cause `fpdec` to use the standard
  library, so that conversion to string, formatting and printing are
  available. When disabled, the use of crate `alloc` together with a
  system-specific allocator is needed to use that functionality.

* **packed** - When enabled, the struct `Decimal` is marked with
  `#[repr(packed)]`.

### Optional dependencies

* **num-traits** - When enabled, the trait `num-traits::Num` is implemented
  for `Decimal`.

* **serde-as-str** - When enabled, support for `serde` is enabled. This allows
  `Decimal` instances to be serialzed as strings and to be deserialized from
  strings via `serde`.

* **rkyv** - When enabled, support for `rkyv` is enabled. This allows
  `Decimal` instances to be zero-copy serialized and deserialized via
  `rkyv` archives.
