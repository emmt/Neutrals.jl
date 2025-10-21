# User visible changes in `Neutrals`

This page describes the most important changes in `Neutrals`. The format is based on [Keep
a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic
Versioning](https://semver.org).

## Unreleased

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
