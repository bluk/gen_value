# Changelog

## [0.5.0] - 2022-04-18

### Updated

- Rename UnmanagedGenVec::set_gen to set_next_gen

  Panic if set_next_gen is called with more than next gen

  UnmanagedGenVec.set_next_gen() must be called with the next generation of
  the generational index. It is a logical error to call with generations
  further ahead.

  The method can only set the generation to the next generation so
  rename the method to better reflect the intent and capability.

- Rename UnmanagedGenVec::push to push_with_gen

  Add push() with default generation

- Panic on remove with last generation

  For a managed indexes GenVec, the last generation is a tombstone
  value which should never be returned. However, if the value were
  manually constructed and used with remove, the method should panic to
  indicate the program logic is incorrect because the value will remain
  accessible

- Use usize for default generation type

  Due to using a usize for the index type, using a smaller type for the
  generation does not result in any memory savings (unless the
  generational index type uses something besides the default (I, G)
  tuple in a packed or space savings encoding).
  Generally to save space, both the Index type and the Generation type
  must be considered together so default to "expected" behavior while
  callers can still customize behavior for their needs.

## [0.4.0] - 2022-04-15

### Updated

- Only allow set if the generations are equal

  The generation in the Vec should always be the greatest generation
  used. A generational index with a greater generation is
  invalid. While it could be allowed, skipping generations should
  be considered a logic bug because it wastes generations.

  IndexMut implementations are added for `GenVec` and `UnmanagedGenVec`.

- Fix inconsistent error/panic in set vs set_or_push

  If the index is out of bounds when calling set_or_push,
  an error is returned instead of panicing.

- Fix default GenIndex type for UnmanagedGenVec

  Type parameter specified (usize, u16) but should have been (I, G)
  in case G or I is specified and they do not match the defaults.

## [0.3.0] - 2022-04-15

### Updated

- Use the maximum generation value as a tombstone value to indicate an index
  can no longer be accessed or used. Add `Incremental::max` and changes
  to `Allocator::dealloc`.

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

[Unreleased]: https://github.com/bluk/gen_value/compare/v0.5.0...HEAD
[0.5.0]: https://github.com/bluk/gen_value/compare/v0.4.0...v0.5.0
[0.4.0]: https://github.com/bluk/gen_value/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/bluk/gen_value/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/bluk/gen_value/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/bluk/gen_value/releases/tag/v0.1.0