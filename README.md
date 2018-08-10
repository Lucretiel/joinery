# joinery
A Rust library for generically joining iterables with a separator. Provides the tragically missing string join functionality to rust.

```rust
extern crate joinery;

use std::env;

// Or use joinery::prelude::*;
use joinery::Joinable;

fn main() {
	// Join things!
	println!("{}", ["Hello", "World!"].iter().join_with(", "));

	// Join things of different types!
	println!("{}", ["Hello", "World!"].iter().join_with(' '));
	println!("{}", (0..10).join_with(' '));
}
```

## Installation

Add joinery to your `Cargo.toml`:

```toml
[dependencies]
joinery = "1.0.0"
```

### Nightly-only features

joinery supports various nightly-only optimization features, such as `iter::TrustedLen` and `Iterator::try_fold` (which requires `ops::Try`). These features are enabled with the `"nightly"` cargo feature:

```toml
[dependencies.joinery]
version = "1.0.0"
features = ["nightly"]
```

Note that, because nightly-only features are unstable, joinery can't make any stability guarentees about their continued presence or interface consistency between versions. While we'll do our best to preserve compatibility, we only guarentee semver compatibility for the non-nightly interface.

## Overview

Joinery provides joins over iterators. Put simply, a join is a combination of an iterator and a separator. The join then conceptually represents all the elements of the iterator, with the separator between each one.

You can create a join with the `join_with` method, which is defined for all `IntoIterator` types via the `Joinable` trait:

```rust
use joinery::prelude::*;

let content = vec![1, 2, 3, 4, 5];

let join = content.iter().join_with(", ");
```

Joins implement `Display`, so they can be written to writers or converted into strings. Joins are stateless, so they can be reused, assuming that the underlying iterator is cloneable:

```rust
println!("Comma-separated numbers: {}", join);

let mut result = String::new();
write!(&mut result, "{}", join);

// Don't forget that `Display` gives you `ToString` for free!
let result2 = join.to_string();
```

Joins are also iterable. You can use `.iter()` to iterate over references to the underlying iterator, or `into_iter()` to convert the join into an iterator. Join iterators use an item type called `JoinItem`, which distinguishes between separators and elements of the underlying iterator:

```rust
use joinery::JoinItem;
let mut iter = join.iter();

assert_eq!(iter.next(), Some(JoinItem::Element(&1)));
assert_eq!(iter.next(), Some(JoinItem::Separator(&", ")));
assert_eq!(iter.next(), Some(JoinItem::Element(&2)));
assert_eq!(iter.next(), Some(JoinItem::Separator(&", ")));
assert_eq!(iter.next(), Some(JoinItem::Element(&3)));
```

See the [docs](https://docs.rs/joinery) for complete documentation, including many more examples.
