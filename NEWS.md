# User visible changes in `Neutrals`

This page describes the most important changes in `Neutrals`. The format is based on [Keep
a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic
Versioning](https://semver.org/spec).

## Unreleased

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
