# Neutrals
[![Build Status](https://github.com/emmt/Neutrals.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/emmt/Neutrals.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/emmt/Neutrals.jl?svg=true)](https://ci.appveyor.com/project/emmt/Neutrals-jl)
[![Coverage](https://codecov.io/gh/emmt/Neutrals.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/emmt/Neutrals.jl)
[![Aqua QA](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)

This package provides two singleton values, `𝟘` and `𝟙` which are the respective *neutral
elements* for the addition and multiplication of numbers regardless of their types. In
other words, whatever the type and value of the number `x`, `𝟘 + x` and `𝟙*x` yields `x`
unchanged and without computations. Hence, `𝟘 + x === x` and `𝟙*x === x` hold even though
`x` is not an instance of `isbitstype` like `BigInt` or `BigFloat`. Besides, `𝟘` is a
so-called *strong zero* which means that `𝟘*x` always yields `𝟘` without computations. In
particular, `𝟘*Inf` and `𝟘*NaN` both yield `𝟘`. Since `𝟘` and `𝟙` are singletons, their
specific behaviors in arithmetic operations is inferable at compile time and can result in
valuable optimizations.

Consistent rules for the subtraction and division follow from the rules for the addition
and multiplication with `𝟘` or `𝟙`. For example, `-𝟙`, the opposite of `𝟙`, is also a
singleton whose effect in a multiplication is to negate the other operand: `(-𝟙)*x` always
yields `-x`.

Table of contents:
* [Compatibility](#compatibility)
* [Binary Operations](#binary-operations)
  * [Addition](#addition)
  * [Subtraction](#subtraction)
  * [Multiplication](#multiplication)
  * [Division](#division)
  * [`div`, `rem`, and `mod`](#div-rem-and-mod)
  * [Bitwise Binary Operations](#bitwise-binary-operations)
  * [Bit-shift Operations](#bit-shift-operations)
  * [Comparisons](#comparisons)
* [Conversion Rules](#conversion-rules)
* [Broadcasting Rules](#broadcasting-rules)
* [Ranges](#ranges)
* [Dimensionful Quantities](#dimensionful-quantities)
* [Miscellaneous](#miscellaneous)
* [Related packages](#related-packages)


## Compatibility

Before version 1.3 of Julia, `𝟘` and `𝟙` cannot be used as names of constants, the aliases
`ZERO` and `ONE` can be used instead.

## Binary operations

This section describes the rules involving a neutral number and any other number. For
[commutative operations](https://en.wikipedia.org/wiki/Commutative_property) like the
multiplication (`*`), the addition (`+`), binary bitwise operations (`|`, `&`, and `xor`
or `⊻`), and the comparison for equality (`==`), the same rules apply if the operand are
exchanged.

### Addition

The following rules apply for the addition involving a neutral number and any
dimensionless number `x`:

``` julia
x + 𝟘 -> x
x + 𝟙 -> x + one(x)
x + (-𝟙) -> x - one(x)
```

The result of an addition with a neutral number has the same type as `x`, except if `x` is
a Boolean and the neutral number is `±𝟙` which yield an `Int` (as does the addition of
Booleans in Julia).

### Subtraction

The rules for the subtraction involving a neutral number and any dimensionless number `x`
follow from those of the addition:

``` julia
x - 𝟘 -> x
𝟘 - x -> -x
x - 𝟙 -> x - one(x)
𝟙 - x -> one(x) - x
x - (-𝟙) -> x + one(x)
(-𝟙) - x -> -one(x) - x
```

### Multiplication

The following rules apply for the multiplication of a neutral number and a number `x`:

``` julia
𝟘*x -> 𝟘         # if `x` is dimensionless
𝟘*x -> 𝟘*unit(x) # if `x` is dimensionful
𝟙*x -> x
-𝟙*x -> -x
```

If `x` is dimensionful, the result has the same dimensions as `x`. For example:

``` julia
julia> using Neutrals, Unitful.DefaultSymbols

julia> 𝟘*3
𝟘

julia> 𝟘*(3kg)
𝟘 kg

```


### Division

The rules for the division involving a neutral number and any number `x` follow from those
of the multiplication:

``` julia
𝟘/x -> 𝟘         # if `x` is dimensionless
𝟘/x -> 𝟘/unit(x) # if `x` is dimensionful
𝟙/x -> inv(x)
-𝟙*x -> -inv(x)
x/𝟘 -> DivideError
x/𝟙 -> x
x/-𝟙 -> -x
```


### `div`, `rem`, and `mod`

Similar rules are implemented for the quotient and remainder of the truncated division
(`div` or `÷` and `rem` or `%`) and for the modulo (`mod`). In Julia, for `x` and `y`
integers `div(x, y)` and `rem(x, y)` yield a result of the signedness of `x`, while
`mod(x, y)` yields a result of the signedness of `y`. This rule is preserved when one of
the operand is a neutral number, considering that neutral numbers are signed integers.

For `div`, `rem`, and `mod` when one operand is a Boolean and the other is a neutral
number the behavior implemented in Julia for Booleans is reflected. This implies that the
neutral number be converted into a `Bool`. Hence, if the neutral operand is `-𝟙`, an
`InexactError` is thrown.


### Bitwise Binary Operations

In binary bitwise operations `|`, `&`, and `xor` (also denoted `⊻`) between an integer `i`
and a neutral number `n`, the implemented rules are such that the result is as if `𝟘` and
`𝟙` are converted to the type of `i` while `-𝟙` is assumed to represent a bit mask of the
same type as `i` with all bits set to `1`, that is `~zero(i)`. For a given binary bitwise
operation denoted by `⋄`, this corresponds to the following rules:

``` julia
i ⋄  𝟘 -> i ⋄ zero(i)
i ⋄  𝟙 -> i ⋄ one(i)
i ⋄ -𝟙 -> i ⋄ ~zero(i)
```

These rules may be optimized in the implementation. For example:

``` julia
i |  𝟘 -> i
i | -𝟙 -> ~zero(i)
i &  𝟘 -> zero(i)
i & -𝟙 -> i
i ⊻  𝟘 -> i
```

It may be noted that, `i & 𝟘` yields `zero(i)` and not `𝟘` as would do `i*𝟘`. This is
because `𝟘` is defined relatively to the addition and the multiplication (`+` and `*`),
not the *bitwise-and* operation (`&`).


### Bit-shift Operations

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
while bit shifting `x` by `±𝟙` bit shifts `x` by one bit in the correct direction where
`UInt(1)` is to dispatch on the type of `x` not on that of the number of bits. This
closely reflects the behavior implemented in `base/int.jl` except that bit-shifting by `𝟘`
always yields the left operand  unchanged even though it is a Boolean.


### Comparisons

When comparing values with `==`, `<`, `<=`, `isequal`, `isless`, and `cmp`, the rule of
thumb is that the behavior shall reflect the expression. This poses no problem for `𝟘` and
`𝟙` which are representable by any numeric type. This is not the case of `-𝟙` which
cannot be simply converted to a Boolean, an unsigned number (integer, rational, or
complex).

If `u` is an unsigned number, the following identities hold:

``` julia
u == -𝟙 -> false
u != -𝟙 -> true
isequal(u, -𝟙) -> false
```

Of course, these binary operators being symmetric, their result does not depend on the
order of the arguments.

Furthermore, if `u` is an unsigned real (i.e., not a complex), then:

``` julia
u < -𝟙 -> false
u ≤ -𝟙 -> false
u > -𝟙 -> true
u ≥ -𝟙 -> true
isless(u, -𝟙) -> false
isless(-𝟙, u) -> true
cmp(u, -𝟙) -> 1
cmp(-𝟙, u) -> -1
```


## Conversion Rules

As for other numbers, a neutral number `n` (`𝟘`, `𝟙`, or `-𝟙`) can be converted into a
numeric type `T` by `T(n)` which yields a value of type `T`. This operation is always
successful for `𝟘` and `𝟙` which are representable by any numeric type. For `-𝟙`, an
`InexactError` exception is thrown if `T` is not a signed type, this includes Booleans,
unsigned integers, but also rationals and complexes with Boolean or unsigned parts. As for
any non-big integer, `AbstractFloat(n)` and `float(n)` both yield `n` converted to
`Float64`.

The expression `n % T` can also be used to *convert* a neutral number `n` to an integer
type `T` modulo the number of integers representable in `T`. In this case, `-𝟙 % T` works
even though `T` is unsigned. For example:

``` julia
julia> -𝟙 % UInt16
0xffff

```

The method `convert(T, n)` with `T` a numeric type and `n` a neutral number amounts to
calling `T(n)`. As a result, a neutral number `n` is automatically converted to a value of
type `T` when stored in an array whose elements are of type `T` or when assigned to a
field of type `T` in a mutable structure. For example, assuming `x` is an array of
numbers, it can be zero-filled by:

``` julia
for i in eachindex(x); x[i] = zero(eltype(x)); end
```

which, provided `eltype(x)` is dimensionless, can be written as:

``` julia
for i in eachindex(x); x[i] = 𝟘; end
```

or, better, as:

``` julia
for i in eachindex(x); x[i] *= 𝟘; end
```

which works whether `eltype(x)` is dimensionful or dimensionless.


## Broadcasting Rules

Some broadcasted operations involving a neutral number and a number or an array of numbers
`x` are optimized to return `x` unchanged:

``` julia
x .+ 𝟘 -> x # idem for 𝟘 .+ x -> x
x .- 𝟘 -> x
𝟙 .* x -> x # idem for x .* 𝟙
x ./ 𝟙 -> x
x .^ 𝟙 -> x
```

In addition, if `x` has integer element type, then:

``` julia
x .÷ 𝟙    -> x
x .| 𝟘    -> x # idem for 𝟘 .| x
x .& (-𝟙) -> x # idem for (-𝟙) .& x
x .⊻ 𝟘    -> x # idem for 𝟘 .⊻ x -> x
x .<< 𝟘   -> x
x .>> 𝟘   -> x
x .>>> 𝟘  -> x
```

Other broadcasted operations should work as can be inferred from the rules for numbers.

For multiplying or dividing an array of numbers by neutral numbers, you may
directly use the `*`, `/`, or `\` operators instead of `.*`, `./`, or `.\`:

``` julia
𝟘*x -> similar(x, typeof(𝟘*unit(eltype(x))))
𝟙*x -> x
𝟙\x -> x
x/𝟙 -> x
(-𝟙)*x -> -x
(-𝟙)\x -> -x
x/(-𝟙) -> -x
```

Note that `𝟘*x` is a lightweight array (`sizeof(𝟘*x) = 0`) whose elements are all equal to
the singleton `𝟘` if `eltype(x)` is dimensionless or to the singleton `𝟘*unit(eltype(x))`
if `eltype(x)` is dimensionful (see [Dimensionful Quantities](#dimensionful-quantities)).


## Ranges

Ranges can be constructed with neutral numbers specified as the start, step, and/or stop
parameters of the range. `𝟙:stop` is identical to `Base.OneTo(stop)` if `stop` is a
non-neutral integer or is `𝟙` and is identical to `Base.OneTo(Int(stop))` otherwise.
`start:𝟙:stop` identical to `start:stop` whatever, `start` and `stop`.  Examples:

``` julia
𝟙:6 -> Base.OneTo(6)
3:𝟙:6 -> 3:6
collect(𝟘:𝟘) -> [𝟘]
collect(𝟙:𝟙) -> [𝟙]
```

## Dimensionful Quantities

Neutral numbers can work with dimensionful numbers provided the `Neutrals` package be
properly extended for such numbers and provided the operation makes sense (e.g., adding
`𝟘` to a length in meters does not make sense because `𝟘` is dimensionless).

This is the case of the [`Unitful`](https://github.com/PainterQubits/Unitful.jl)
quantities. For example:

``` julia
using Unitful, Unitful.DefaultSymbols
x = 3kg
𝟘*x === 𝟘*unit(x)         # true
𝟙*x === x                 # true
-𝟙*x == -x                # true
x + 𝟘                     # error, 𝟘 is dimensionless
x + 𝟘*unit(x) == x        # true
x - 𝟘                     # error, 𝟘 is dimensionless
x - 𝟘*unit(x) == x        # true
𝟘*unit(x) == zero(x)      # true
𝟘*unit(x) !== zero(x)     # true
𝟙*unit(x) == oneunit(x)   # true
𝟙*unit(x) !== oneunit(x)  # true
-𝟙*unit(x) == -oneunit(x) # true
𝟙 == one(x)               # true
𝟙 !== one(x)              # true
```

Note that `𝟘*unit(x)` is equal but not identical to `zero(x)` because it is `𝟘` with the
unit of `x`.


## Miscellaneous

`Complex(x,y)` and `complex(x,y)` yield the same result as `x + y*im` even though `x` or
`y` is a neutral number.


## Related Packages

- In base Julia, `false` behaves as a strong zero when multiplied by a float. Moreover it
  preserves the sign of the other operand, e.g. `false*(-NaN)` yields `-0.0`. The sign is
  not preserved in the multiplication by `𝟘` which yields `𝟘`.

- [`Zeros.jl`](https://github.com/perrutquist/Zeros.jl) was a source of inspiration to
  improve `Neutrals.jl`. `Zeros.jl` provides `Zero()` and `One()` which are also strong
  neutral elements for addition and multiplication with numbers. `Zero()` and `One()` are
  similar to `𝟘` or `ZERO`, and `𝟙` or `ONE`. However, `-One()` yields `-1` which is not a
  singleton, division by `One()` converts the other operand to floating-point,
  multiplication of a dimensionful number and `Zero()` is not supported, etc.

- [`StaticNumbers.jl`](https://github.com/perrutquist/StaticNumbers.jl) is a generalization
  of `Zeros` to other any numeric values, not just `0` and `1`.
