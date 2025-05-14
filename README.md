# Neutrals [![Build Status](https://github.com/emmt/Neutrals.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/emmt/Neutrals.jl/actions/workflows/CI.yml?query=branch%3Amain) [![Build Status](https://ci.appveyor.com/api/projects/status/github/emmt/Neutrals.jl?svg=true)](https://ci.appveyor.com/project/emmt/Neutrals-jl) [![Coverage](https://codecov.io/gh/emmt/Neutrals.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/emmt/Neutrals.jl)

This package provides two singleton values, `ZERO` and `ONE`, which are *neutral elements*
for the addition and multiplication of numbers respectively. In other words, whatever the
type and value of the number `x`, `ZERO + x` and `ONE*x` yields `x` unchanged and without
computations. Even though `x` is not an instance of `isbitstype`, `ZERO + x === x` and
`ONE*x === x` hold. Besides, `ZERO` is a so-called *strong zero* which means that `ZERO*x`
always yields `ZERO` without computations. In particular, `ZERO*Inf` and `ZERO*NaN` both
yield `ZERO`. Since `ZERO` and `ONE` are singletons, their specific behaviors in
arithmetic operations is inferable at compile time and can result in valuable
optimizations.

`-ONE`, the opposite of `ONE`, is also a singleton whose effect in a multiplication is to
negate the other operand: `(-ONE)*x` always yields `-x`.

Consistent rules for the subtraction and division follow from the rules for the addition and multiplication.

## Related packages

- [`Zeros`](https://github.com/perrutquist/Zeros.jl) provides `Zero()` and `One()` which
  are also strong neutral elements for addition and multiplication with numbers. `Zero()`
  and `One()` are similar to `ZERO` and `ONE`. However `-One()` yields `-1` which not a
  singleton. Division by `One()` converts the other operand to floating-point.

- [`StaticNumbers`](https://github.com/perrutquist/StaticNumbers.jl).
