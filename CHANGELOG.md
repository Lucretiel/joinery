# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html).

This changelog was added after the release of 1.0.0; changes before that are left undocumented.

## 3.1.0

### Internal

- Added optimized implementations of `Iterator::last` and `Iterator::count`

## 3.0.0

Removed some methods to allow for a more efficient implementation of `JoinIter`. If you weren't using `peek` or `peek_item` you should be able to upgrade without issue.

### Changed

- More efficient implementation of `JoinIter`. No more reduntant states allows for a manual `try_fold` implementation, at the cost of the `peek` family of methods
- Now using Edition 2021
- No longer need to use the `private::Display<'a>` hack

### Removed

- Removed `peek` and `peek_item`
- Removed `syn` dependency

## 2.1.0

### Added

- Added `token-stream` feature which, when enabled, provides a `ToTokens` implementation to `Join`. This allows `Join` objects to be used as lazy token streams in `quote`.
- 0-size `Display` type for `Newline` in `separators`.

## 2.0.0

2019-02-10

Major redesign of library. Most idiomatic joinery code should continue to work, but most of the library's traits and structs have been completely redesigned. The most significant change is that joinery is no longer primarily based on cloneable iterators, but rather on referentially iterable collections; that is, types for which `&'a Container: IntoIterator`. This means that we can get rid of a lot of the weird cruft related to `partial_clone`, etc.

### Design notes:

- Iterators and collections are now treated separately. The `Join` struct is now based on collections, which are types which implement referential iteration (that is, for which `&T: IntoIterator`).
- Iterators can be adapted into `Join` instances via the `CloneIterator` adapter, which adds `&T: IntoIterator` to types that are `T: Clone + Iterator`.
- While the types have drastically changed, idiomatic code (which imports the prelude and uses mainly the `join_with` method) should continue to function
  correctly.

### Changed

- Split the library into various modules for the different functionality.
  - `join` contains the `Join` type and related traits.
  - `iter` contains the `JoinIter` type and related traits and structs.
  - `separators` contains various convenient 0-size `Display` types for common separators, like `Comma` and `Space`.

### Added

- `JoinableIterator` trait, which allows joining iterators directly via `iter_join_with`, or adapting them into `Join` structs via `join_with`
- Added numerous extra 0-size separator types, like `Comma` and `Space`, for common separators.
- Advanced to Rust 2018 Edition.

### Removed

- `NoSeparator` removed from the prelude, since it's generally preferable to use `join_concat`
- Many methods on `Join` were deemed too niche and removed as part of the redesign, such as `partial_clone` and `consume_fmt`.

## 1.2.2

2018-09-15

### Minor

- Various optimizations and simplifications
- Extra test
- Added cargo categories

## 1.2.1

2018-09-10

### Minor

- Fixed broken documentation links

## 1.2.0

2018-09-10

### Changed

- Joinery is now `#![no_std]`

## 1.1.2

2018-08-23

### Minor

- Fixed broken link in docs

## 1.1.1

2018-08-23

### Minor

- Cleaned up the README badges

## 1.1.0

2018-08-23

### Added

- Empty separators:
  - Added `NoSeparator`, a zero-size type which allows users to idiomatically join an iterator without any separator.
  - Added `join_concat`, a helper method for separator-free joins.

### Removed

- Removed `try_fold` after discovering serious implementation bug.
  - Added test demonstrating this bug
  - Would like to re-add someday, but seems difficult or impossible.
  - Note that Iterator still provides `try_fold`; the only thing being removed is the specialized implementation.

### Minor

- Small documentation fix (#12)
- Added README badges

## 1.0.0

2018-08-10

First major release.
