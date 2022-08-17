//! 0-size types for common separators
//!
//! This modules provides [`Display`](https://doc.rust-lang.org/std/fmt/trait.Display.html)-implementing
//! types for common separators. These types are 0-size, with fixed `Display` implementations,
//! intended to aid with compiler optimization.

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
/// See also the [`join_concat`](crate::Joinable::join_concat) method.
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

#[cfg(feature = "token-stream")]
impl quote::ToTokens for NoSeparator {
    fn to_tokens(&self, _tokens: &mut proc_macro2::TokenStream) {}
}

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
    ($($Name:ident(sep: $sep:expr, repr: $repr:expr, test: $test_name:ident $(, token: $($token:tt)?)? ))+) => {$(
        #[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
        #[must_use]
        #[doc = "Zero size type representing the "]
        #[doc = $repr]
        #[doc = " separator."]
        pub struct $Name;

        impl Display for $Name {
            #[inline]
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                $sep.fmt(f)
            }
        }

        impl Separator for $Name {}

        $(
            #[cfg(feature="token-stream")]
            impl quote::ToTokens for $Name {
                fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
                    $(
                        tokens.extend(token!($token));
                    )?
                    let _tokens = tokens;
                }
            }
        )?

        #[cfg(test)]
        mod $test_name {
            use crate::separators::$Name;
            use crate::join::Joinable;

            #[test]
            fn separator() {
                let data = [1, 2, 3];
                let join = data.join_with($Name);
                let result = join.to_string();

                assert_eq!(result, concat!(1, $sep, 2, $sep, 3));
            }

            $(
                #[cfg(feature="token-stream")]
                #[test]
                fn to_tokens() {
                    use quote::{ToTokens, quote};

                    let data = [1, 2, 3];
                    let join = data.join_with($Name);
                    let result = join.into_token_stream();

                    let target = quote! {
                        1i32 $($token)? 2i32 $($token)? 3i32
                    };

                    assert_eq!(result.to_string(), target.to_string());
                }
            )?
        }
    )+}
}

#[cfg(feature = "token-stream")]
macro_rules! token {
    (.) => { token!(token '.') };
    (,) => { token!(token ',') };
    (/) => { token!(token '/') };
    (-) => { token!(token '-') };

    (token $token:literal) => {
        [proc_macro2::TokenTree::Punct(proc_macro2::Punct::new(
            $token,
            proc_macro2::Spacing::Alone,
        ))]
    };
}

const_separator! {
    Newline(sep: '\n', repr: "newline", test: test_newline, token: )
    Space(sep: ' ', repr:"space", test: test_space, token: )
    Comma(sep: ',', repr: "`,`", test: test_comma, token: ,)
    CommaSpace(sep: ", ", repr: "comma followed by space", test: test_comma_space, token: ,)
    Dot(sep: '.', repr: "`.`", test: test_dot, token: .)
    Slash(sep: '/', repr: "`/`", test: test_slash, token: /)
    Underscore(sep: '_', repr: "`_`", test: test_underscore)
    Dash(sep: '-', repr: "`-`", test: test_dash, token: -)
    Tab(sep: '\t', repr: "tab", test: test_tab, token: )
}
