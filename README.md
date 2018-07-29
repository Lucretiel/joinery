# joinery
A Rust library for generically joining iterables with a separator. Provides the tragically missing string join functionality to rust.

```rust
extern crate joinery;

use std::env;

// Or use joinery::prelude::*;
use joinery::Joinable;

fn main() {
	// Join things!
	println!(["Hello", "World!"].iter().join_with(", "));

	// Join things of different types!
	println!(["Hello", "World!"].iter().join_with(' '));
	println!((0..10).join_with(' '));
}
```

## Installation

Add joinery to your `Cargo.toml`:

```toml
[dependencies]
joinery = "0.1.0"
```

### Nightly-only features

If you're using nightly rust, add the features to support nightly-only optimizations:

```toml
[dependencies.joinery]
version = "0.1.0"
features = ["trusted_len", "try_fold"]
```

## Overview

Joinery provides joins over iterators. Put simply, a join is a combination of an iterator and a separator. The join then conceptually represents all the elemetns of the iterator, with the separator between each one.

Joins implement the [`Display`](https://doc.rust-lang.org/std/fmt/trait.Display.html) trait, so they can be printed to writers or [coverted to `String`s](https://doc.rust-lang.org/std/string/trait.ToString.html). They can also be iterated over, and use the `JoinItem` enum to distinguish iterator elements from the separators.

See the docs for complete documentation, including many more examples.
