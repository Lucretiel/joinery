//! 0-size types for common separators
//!
//! This modules provides `Display` types for common separators. These types are
//! 0-size, with fixed `Display` implementation, intended to aid with compiler
//! optimization.

// NOTE: we hope that the compiler will detect that most operations on NoSeparator
// are no-ops, and optimize heavily, because I'd rather not implement a separate
// type for empty-separator-joins.

use core::fmt::{self, Display, Formatter};
use crate::join::Separator;

/// Zero-size type representing the empty separator.
///
/// This struct can be used as a separator in cases where you simply want to
/// join the elements of a separator without any elements between them.
///
/// See also the [`join_concat`](join@Joinable::join_concat) method.
///
/// # Examples
///
/// ```
/// use joinery::JoinableIterator;
/// use joinery::separators::NoSeparator;
///
/// let parts = (0..10);
/// let join = parts.join_with(NoSeparator);
/// assert_eq!(join.to_string(), "0123456789");
/// ```
///
/// *New in 1.1.0*
#[derive(Debug, Clone, Copy, Default)]
#[must_use]
pub struct NoSeparator;

impl Display for NoSeparator {
    #[inline(always)]
    fn fmt(&self, _f: &mut Formatter) -> fmt::Result {
        Ok(())
    }
}

impl Separator for NoSeparator {}

#[cfg(test)]
#[test]
fn test_no_separator() {
    use crate::join::Joinable;
    use crate::separators::NoSeparator;

    let data = [1, 2, 3, 4, 5];
    let join = data.join_with(NoSeparator);
    let result = join.to_string();

    assert_eq!(result, "12345");
}

macro_rules! const_separator {
    ($($Name:ident: $sep:expr => $test_name:ident,)+) => {$(
        #[derive(Debug, Clone, Copy, Default)]
        #[must_use]
        pub struct $Name;

        impl Display for $Name {
            #[inline]
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                $sep.fmt(f)
            }
        }

        impl Separator for $Name {}

        #[cfg(test)]
        #[test]
        fn $test_name() {
            use crate::separators::$Name;
            use crate::join::Joinable;

            let data = [1, 2, 3];
            let join = data.join_with($Name);
            let result = join.to_string();

            assert_eq!(result, concat!(1, $sep, 2, $sep, 3));
        }
    )+}
}

const_separator! {
    Space: ' ' => test_space,
    Comma: ',' => test_comma,
    CommaSpace: ", " => test_comma_space,
    Dot: '.' => test_dot,
    Slash: '/' => test_slash,
    Underscore: '_' => test_underscore,
    Dash: '-' => test_dash,
    Tab: '\t' => test_tab,
}
