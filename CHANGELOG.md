# Changelog

## [0.2.0] - 2022-04-14

### Updated

- Added type parameters to `UnmanagedGenVec` for the index `I` and the
  generational index type `GenIndex`. Adding the types constrains the
  generational index to one type improving overall safety at the cost
  of some flexibility.
- Renamed `Index` type parameter in `GenVec` to `GenIndex`.

## [0.1.0] - 2022-04-14

### Added

- Initial release

[Unreleased]: https://github.com/bluk/gen_value/compare/v0.1.0...HEAD
[0.2.0]: https://github.com/bluk/gen_value/releases/tag/v0.1.0...v0.2.0
[0.1.0]: https://github.com/bluk/gen_value/releases/tag/v0.1.0