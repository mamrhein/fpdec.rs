This crate strives to provide a fast implementation of `Decimal` fixed-point 
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
At the binary level a Decimal number is represented as a coefficient (stored 
as an `i128` value) combined with a precision specifying the number of 
fractional decimal digits.
### Status
Experimental (work in progess)
