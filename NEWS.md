# User visible changes in `Neutrals`

This page describes the most important changes in `Neutrals`. The format is based on [Keep
a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic
Versioning](https://semver.org/spec).

## Unreleased

### Fixed

- Fixes for irrationals in all Julia versions

- Documentation for `𝟙`.

- Improve documentation.

### Added

- Extend addition and subtraction with neutrals to `Number`.

### Changed

- Extending `Neutral.impl_conv` is easier: it is sufficient to extend this method for a
  foreign numeric type and just `Neutral`, not for each instance of `Neutral`.
