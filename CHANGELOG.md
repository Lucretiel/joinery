# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html).

This changelog was added after the release of 1.0.0; changes before that are left undocumented.

## Unreleased

Major redesign of library. Most idiomatic joinery code should continue to work, but most of the library's traits and structs have been completely redesigned. The most significant change is that joinery is no longer primarily based on cloneable iterators, but rather on referentially iterable containers; that is, types for which `&'a Container: IntoIterator`. This means that we can get rid of a lot of the weird cruft related to `partial_clone`, etc.

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
