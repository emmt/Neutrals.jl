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

## Bitwise binary operations

In binary bitwise operations `|`, `&`, and `xor` (also denoted `⊻`) between an integer `i`
and a neutral number `n`, the implemented rules are such that the result is as if `𝟘` and
`𝟙` are converted to the type of `i` while `-𝟙` is assumed to represent a bit mask of the
same type as `i` with all bits set to `1`. For a given binary bitwise operation denoted by
`⋄`, this corresponds to the following rules:

``` julia
i ⋄  𝟘 -> i ⋄ zero(i)
i ⋄  𝟙 -> i ⋄ one(i)
i ⋄ -𝟙 -> i ⋄ (i isa Bool ? true : -one(i))
```

Note that all bitwise binary operations are commutative: their result does not depend on
the order of the operands.

These rules may be optimized in the implementation. for example:

``` julia
i |  𝟘 -> i
i &  𝟘 -> zero(i)
i & -𝟙 -> i
i ⊻  𝟘 -> i
```

## Bit-shift operations

In Julia, bit-shifting integer `x` by `n` bits yields a result of the same type as `x`
except for Booleans for which the result is an `Int`. With the `Neutrals` package, if `n`
is a neutral number (`𝟘`, `𝟙`, or `-𝟙`), the following rules are implemented:

``` julia
x <<   𝟘 -> x
x <<   𝟙 -> x << UInt(1)
x <<  -𝟙 -> x >> UInt(1)
x >>   𝟘 -> x
x >>   𝟙 -> x >> UInt(1)
x >>  -𝟙 -> x << UInt(1)
x >>>  𝟘 -> x
x >>>  𝟙 -> x >>> UInt(1)
x >>> -𝟙 -> x << UInt(1)
```

These rules provide two optimizations: bit shifting `x` by `𝟘` bits leaves `x` unchanged,
while bit shifting `x` by `±𝟙` shifts `x` by one bit in the correct direction where
`UInt(1)` is to dispatch on the type of `x` not on that of the number of bits. This
closely reflects the behavior implemented in `base/int.jl` except that bit-shifting by `𝟘`
always yields the left argument unchanged even though it is a Boolean.

## Rules for conversion

As for other numbers, a neutral number `n` (`𝟘`, `𝟙`, or `-𝟙`) can be converted into a
numeric type `T` by `T(n)` or equivalently by `convert(T, n)` with both yield the same
result of type `T`. This operation is always successful for `𝟘` and `𝟙` which are
representable by any numeric type. For `-𝟙`, an `InexactError` exception is thrown if `T`
is not a signed type this includes Booleans, unsigned integers, but also rationals and
complexes with Boolean or unsigned parts.

## Related packages

- [`Zeros`](https://github.com/perrutquist/Zeros.jl) provides `Zero()` and `One()` which
  are also strong neutral elements for addition and multiplication with numbers. `Zero()`
  and `One()` are similar to `ZERO` and `ONE`. However `-One()` yields `-1` which not a
  singleton. Division by `One()` converts the other operand to floating-point.

- [`StaticNumbers`](https://github.com/perrutquist/StaticNumbers.jl).
