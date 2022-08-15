#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "nightly", feature(trusted_len))]
#![cfg_attr(feature = "nightly", feature(try_trait_v2))]

//! Joinery provides generic joining of iterables with separators. While it is
//! primarily designed the typical use case of writing to a [writer][core::fmt::Write]
//! or creating a `String` by joining a list of data with some kind of string
//! separator (such as `", "`),  it is fully generic and can be used to combine
//! any iterator or collection with any separator. In this way it is intended
//! to supercede the existing `SliceConcatExt::join` method, which only works
//! on slices and can only join with a matching type.
//!
//! # Examples
//!
//! Create a comma separated list:
//!
//! ```
//! use joinery::Joinable;
//!
//! let result = vec![1, 2, 3, 4].join_with(", ").to_string();
//! assert_eq!(result, "1, 2, 3, 4")
//! ```
//!
//! `write!` a comma-separated list:
//!
//! ```
//! use joinery::Joinable;
//! use std::fmt::Write;
//!
//! let join = vec![1, 2, 3, 4, 5].join_with(", ");
//!
//! let mut result = String::new();
//!
//! write!(&mut result, "Numbers: {}", join);
//! assert_eq!(result, "Numbers: 1, 2, 3, 4, 5");
//!
//! // Note that joins are stateless; they can be reused after writing
//! let result2 = join.to_string();
//! assert_eq!(result2, "1, 2, 3, 4, 5");
//! ```
//!
//! Join any iterator:
//!
//! ```
//! use joinery::JoinableIterator;
//!
//! let join = (0..10)
//!     .filter(|x| *x % 2 == 0)
//!     .map(|x: i32| x.pow(2))
//!     .join_with(", ");
//!
//! let result = join.to_string();
//! assert_eq!(result, "0, 4, 16, 36, 64")
//! ```
//!
//! Iterate over joins:
//!
//! ```
//! use joinery::{Joinable, JoinItem};
//!
//! // Note that the collection values and the separator can be different types
//! let join = ["some", "sample", "text"].join_with(' ');
//! let mut join_iter = (&join).into_iter();
//!
//! assert_eq!(join_iter.next(), Some(JoinItem::Element(&"some")));
//! assert_eq!(join_iter.next(), Some(JoinItem::Separator(&' ')));
//! assert_eq!(join_iter.next(), Some(JoinItem::Element(&"sample")));
//! assert_eq!(join_iter.next(), Some(JoinItem::Separator(&' ')));
//! assert_eq!(join_iter.next(), Some(JoinItem::Element(&"text")));
//! assert_eq!(join_iter.next(), None);
//! ```
//!
//! Display the first 5 consecutive multiples of 1-5 on separate lines:
//!
//! ```
//! use joinery::{Joinable, JoinableIterator};
//! let multiples = 1..=5;
//! let ranges = multiples.map(|m| (1..=5).map(move |n| n * m));
//!
//! let lines = ranges.map(|range| range.join_with(", "));
//! let result = lines.join_with('\n').to_string();
//! assert_eq!(result, "1, 2, 3, 4, 5\n\
//!                     2, 4, 6, 8, 10\n\
//!                     3, 6, 9, 12, 15\n\
//!                     4, 8, 12, 16, 20\n\
//!                     5, 10, 15, 20, 25");
//! ```

pub mod iter;
pub mod join;
pub mod separators;

pub use crate::iter::{JoinItem, JoinIter, JoinableIterator};
pub use crate::join::{Join, Joinable, Separator};

/// The joinery prelude
pub mod prelude {
    pub use crate::iter::JoinableIterator;
    pub use crate::join::Joinable;
}
