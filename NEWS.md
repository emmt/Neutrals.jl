# User visible changes in `Neutrals`

This page describes the most important changes in `Neutrals`. The format is based on [Keep
a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic
Versioning](https://semver.org/spec).


## Unreleased

### Changed

- Broadcasted operations involving a neutral number and a number or an array of numbers `x`
  have been extended to yield `x` unchanged if possible and as an optimization. Other
  broadcasted operations should yield the same result as before.


## Version 0.2.2 (2025/05/26)

### Fixed

- Binary operations between a `Complex{Bool}` and a neutral number behave as documented.

- `-𝟙` behaves as documented in additions, subtractions, and comparisons. In these
  situations the result is as if `-𝟙` be replaced by `-one(x)` where `x` is the other
  operand. The result of the operation is however computed after simplification of the
  resulting expression. For example, expression `x - (-𝟙)` becomes `x - (-one(x))` which
  is simplified in `x + one(x)` (as before) but expression `(-𝟙) - x` is equivalent to
  `-one(x) - x` (after this fix).


## Version 0.2.1 (2025/05/22)

### Fixed

- Ambiguities in binary operations involving a complex and a neutral number.


## Version 0.2.0 (2025/05/21)

### Fixed

- In all bitwise binary operations, `-𝟙` becomes `~zero(T)` with `T` the type of the other
  operand.

- Fixes for irrationals in all Julia versions

- Documentation for `𝟙`.

- Improve documentation.

### Changed

- Extend addition and subtraction with neutrals to `Number`.
