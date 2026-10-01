# User visible changes in `Neutrals`

This page describes the most important changes in `Neutrals`. The format is based on [Keep
a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic
Versioning](https://semver.org).

## Unreleased

Code has been enormously simplified and rules updated to yield more consistent results.
Unitful numbers no longer require specific treatment. As a consequence, there are a few
breaking changes (see below) but in most cases the end-user shall see no differences.


### Breaking changes

- `promote_rule` for a Boolean and a neutral number always yields `Int` (previously, it used
  to yield `Int` for a negative neutral number and `Bool` otherwise).

- Division by `𝟘` no longer throws `DivideError` but rather yields a sensitive result
  considering that `𝟘` is a strong zero:

  - For neutral operands: `𝟘/𝟘 -> NaN`, `𝟙/𝟘 -> Inf`, and  `-𝟙/𝟘 -> -Inf`. This rule
    applies for `inv(𝟘) -> 𝟙/𝟘 -> Inf`.

  - For a non-neutral real number `x`, `x/𝟘 -> ±Neutrals.infinity(x)` that is infinity if
    `x >= 0` or minus infinity if `x < 0` and where `Neutrals.infinity(x)` is the rational
    `one(T)//zero(T)` if `x` is integer of type `T` or rational with numerator and
    denominator of type `T`.

  - For a complex number `z`, `z/𝟘 -> complex(real(z)/𝟘, imag(z)/𝟘)`.

- Non-exported public functions `Neutrals.type_complex` and `Neutrals.type_signed` have been
  suppressed.

- The special rules that `start:𝟙:stop` is identical to `start:stop` and that `𝟙:stop`, with
  `stop` and integer, is identical to `Base.OneTo(stop)` are preserved but building a range
  `start:[step:]stop` with a mixture of reals and neutral numbers now use less esoteric
  rules. In `start:step:stop`, the endpoints `start` and `stop` are first promoted to the
  same type using standard promotion rules and neutral numbers are eventually converted to
  ordinary integers to prevent building ranges of neutral numbers. It is however still
  possible to build a range of neutral numbers by calling the constructors, not with the
  colon `:` operator.

### Changed

- Non-exported public function `Neutrals.value` renamed `Neutrals.static_value`.

### Added

- Bit-shift operations are supported for a leftmost operand which is neutral number. In this
  case, the result is an `Int`. Previously only the right-most operand (the number of bits
  to shift) could be a neutral number.

- New non-exported public functions to deal with correctly taking the opposite of a number.
  `Neutrals.negate(x)` returns `-x` throwing an error if the value of `x` cannot be truly
  negated while `Neutrals.can_be_truly_negated(x)` returns whether `x` can be truly negated
  by `-x`. Only non-zero unsigned numbers (unsigned integers and rationals or complexes with
  unsigned components) cannot be truly negated.

### Fixed

- The division `x/-𝟙` yields `-x` (as before) but an error is thrown if `x` cannot be truly
  negated. Hence, it can be correctly assumed that `x/-𝟙 == x/-1` always holds. Only
  non-zero unsigned numbers (unsigned integers and rationals or complexes with unsigned
  components) cannot be truly negated.

## Version 0.4.1 (2026-07-27)

### Added

- `Base.checked_abs(x::Neutral)` is implemented.

### Fixed

- Some documentation has been fixed and updated.

## Version 0.4.0 (2026-06-11)

### Breaking changes

- `Neutrals` package now requires `TypeUtils` ≥ 2.

### Changed

- Non-exported `Neutrals.is_dimensionless` has been deprecated and replaced by
  `TypeUtils.is_unitless`.

- Non-exported `Neutrals.is_static_number` has been replaced by
  `TypeUtils.is_static_number`.

### Added

- Non-exported public function `Neutrals.dispatch` and type `Neutrals.Dispatch` to mark
  numbers that may lead to code specialization based on their values.

## Version 0.3.5 (2025-12-19)

### Added

- `Neutrals.is_static_number(x)` and `Neutrals.is_static_number(typeof(x))` return whether
  `x` is a *static number*, that is a number whose value is known at compile-time. Being a
  static number is a *trait* that only depends on the type of `x`.

- `Neutrals.recode` and `Neutrals.recode!` to substitute symbols in expressions.

- Macro `@dispatch_on_value sym expr` to generate code that dispatches expression `expr`
  based on the run-time value of the symbol `sym`.


## Version 0.3.4 (2025-10-21)

This new minor version improves compatibility with Julia 1.12 and extends precision methods
of the [`TypeUtils`](https://github.com/emmt/TypeUtils.jl) package.

### Fixed

- Fix list of non-exported public methods (needed for quality testing with `Aqua.jl` and
  for Julia ≥ 1.12).

- Fix ambiguity for `x^n` with `n` a neutral number (needed for Julia ≥ 1.12).

- `TypeUtils.adapt_precision(T, x::Neutral) -> x` and
  `TypeUtils.get_precision(::Type{<:Neutral}) -> AbstractFloat`.


## Version 0.3.3 (2025-06-20)

This version is the first official release.


## Version 0.3.2 (2025-06-20)

### Added

- Tests with [`Aqua.jl`](https://github.com/JuliaTesting/Aqua.jl).

### Changed

- The API of the `Neutral.impl_*` methods implementing binary operations has changed.
  These methods now take a leading argument which is `Val(1)` if only the 1st operand is a
  neutral number, `Val(2)` if only the 2nd operand is a neutral number, and `Val(3)` if
  both operands are neutral numbers.

### Fixed

- Many potential ambiguities have been fixed.


## Version 0.3.1 (2025-05-28)

### Added

- Extend `modf` and `widen` for neutral numbers.

- Arrays of numbers can be efficiently multiplied or divided by neutral numbers.

- Ranges can be constructed with neutral numbers specified as the start, step, and/or stop
  parameters of the range. `𝟙:stop` is identical to `Base.OneTo(stop)` if `stop` is a
  non-neutral integer or is `𝟙` and is identical to `Base.OneTo(Int(stop))` if `staop` is
  another neutral number. `start:𝟙:stop` is identical to `start:stop` whatever, `start` and
  `stop`.

### Fixed

- `Complex(x, y)` and `complex(x, y)` behave as `x + y*im` when at least one of `x` or `y`
  is a neutral number.


## Version 0.3.0 (2025-05-26)

### Changed

- Broadcasted operations involving a neutral number and a number or an array of numbers `x`
  have been extended to yield `x` unchanged if possible and as an optimization. Other
  broadcasted operations should yield the same result as before.


## Version 0.2.2 (2025-05-26)

### Fixed

- Binary operations between a `Complex{Bool}` and a neutral number behave as documented.

- `-𝟙` behaves as documented in additions, subtractions, and comparisons. In these
  situations the result is as if `-𝟙` be replaced by `-one(x)` where `x` is the other
  operand. The result of the operation is however computed after simplification of the
  resulting expression. For example, expression `x - (-𝟙)` becomes `x - (-one(x))` which
  is simplified in `x + one(x)` (as before) but expression `(-𝟙) - x` is equivalent to
  `-one(x) - x` (after this fix).


## Version 0.2.1 (2025-05-22)

### Fixed

- Ambiguities in binary operations involving a complex and a neutral number.


## Version 0.2.0 (2025-05-21)

### Fixed

- In all bitwise binary operations, `-𝟙` becomes `~zero(T)` with `T` the type of the other
  operand.

- Fixes for irrationals in all Julia versions

- Documentation for `𝟙`.

- Improve documentation.

### Changed

- Extend addition and subtraction with neutrals to `Number`.
