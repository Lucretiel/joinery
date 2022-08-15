//! Core join type and related traits

use core::fmt::{self, Display, Formatter};

#[cfg(feature = "token-stream")]
use {proc_macro2::TokenStream, quote::ToTokens};

use crate::{
    iter::{JoinItem, JoinIter, JoinableIterator},
    separators::NoSeparator,
};

/// A trait for converting collections into [`Join`] instances.
///
/// This trait is implemented for all referentially iterable types; that is,
/// for all types for which `&T: IntoIterator`. See [`join_with`][Joinable::join_with]
/// for an example of its usage.
pub trait Joinable: Sized {
    type Collection;
    /// Combine this object with a separator to create a new [`Join`] instance.
    /// Note that the separator does not have to share the same type as the
    /// iterator's values.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::Joinable;
    ///
    /// let parts = vec!["this", "is", "a", "sentence"];
    /// let join = parts.join_with(' ');
    /// assert_eq!(join.to_string(), "this is a sentence");
    /// ```
    fn join_with<S>(self, sep: S) -> Join<Self::Collection, S>;

    /// Join this object with an [empty separator](NoSeparator). When rendered
    /// with [`Display`], the underlying elements will be directly concatenated.
    /// Note that the separator, while empty, is still present, and will show
    /// up if you iterate this instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::Joinable;
    ///
    /// let parts = vec!['a', 'b', 'c', 'd', 'e'];
    /// let join = parts.join_concat();
    /// assert_eq!(join.to_string(), "abcde");
    /// ```
    fn join_concat(self) -> Join<Self::Collection, NoSeparator> {
        self.join_with(NoSeparator)
    }
}

impl<T> Joinable for T
where
    for<'a> &'a T: IntoIterator,
{
    type Collection = Self;

    fn join_with<S>(self, sep: S) -> Join<Self, S> {
        Join {
            collection: self,
            sep,
        }
    }
}

/// A trait for using a separator to produce a [`Join`].
///
/// This trait provides a more python-style interface for performing joins.
/// Rather use [`collection.join_with`][Joinable::join_with], you can instead
/// use:
///
/// ```
/// use joinery::Separator;
///
/// let join = ", ".separate([1, 2, 3, 4]);
/// assert_eq!(join.to_string(), "1, 2, 3, 4");
/// ```
///
/// By default, [`Separator`] is implemented for [`char`] and [`&str`][str], as
/// well as all the separator types in `separators`.
///
/// Note that any type can be used as a separator in a [`Join`] when
/// creating one via [`Joinable::join_with`]. The [`Separator`] trait and its
/// implementations on [`char`] and [`&str`][str] are provided simply as
/// a convenience.
pub trait Separator: Sized {
    fn separate<T: Joinable>(self, collection: T) -> Join<T::Collection, Self> {
        collection.join_with(self)
    }
}

impl Separator for char {}
impl<'a> Separator for &'a str {}

/// The primary data structure for representing a joined sequence.
///
/// It contains a collection and a separator, and represents the elements of the
/// collection with the separator dividing each element. A collection is defined
/// as any type for which `&T: IntoIterator`; that is, any time for which references
/// to the type are iterable.
///
/// A [`Join`] is created with [`Joinable::join_with`], [`Separator::separate`], or
/// [`JoinableIterator::join_with`]. Its main use is an implementation of [`Display`],
/// which writes out the elements of the underlying collection, separated by the
/// separator. It also implements [`IntoIterator`], using a [`JoinIter`].
///
/// # Examples
///
/// Writing via [`Display`]:
///
/// ```
/// use joinery::Joinable;
/// use std::fmt::Write;
///
/// let content = [1, 2, 3, 4, 5, 6, 7, 8, 9];
/// let join = content.join_with(", ");
///
/// let mut buffer = String::new();
/// write!(buffer, "Numbers: {}", join);
///
/// assert_eq!(buffer, "Numbers: 1, 2, 3, 4, 5, 6, 7, 8, 9");
///
/// // Don't forget that `Display` gives to `ToString` for free!
/// assert_eq!(join.to_string(), "1, 2, 3, 4, 5, 6, 7, 8, 9")
/// ```
///
/// Iterating via [`IntoIterator`]:
///
/// ```
/// use joinery::{Separator, JoinItem};
///
/// let content = [0, 1, 2];
/// let join = ", ".separate(content);
/// let mut join_iter = (&join).into_iter();
///
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(&0)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(&", ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(&1)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(&", ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(&2)));
/// assert_eq!(join_iter.next(), None);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct Join<C, S> {
    collection: C,
    sep: S,
}

impl<C, S> Join<C, S> {
    /// Get a reference to the separator.
    pub fn sep(&self) -> &S {
        &self.sep
    }

    /// Get a reference to the underlying collection.
    pub fn collection(&self) -> &C {
        &self.collection
    }

    /// Get a mutable reference to the underlying collection
    pub fn collection_mut(&mut self) -> &mut C {
        &mut self.collection
    }

    /// Consume the join, and return the underlying collection.
    pub fn into_collection(self) -> C {
        self.collection
    }

    /// Consume `self` and return underlying collection and separator.
    pub fn into_parts(self) -> (C, S) {
        (self.collection, self.sep)
    }
}

impl<C, S: Display> Display for Join<C, S>
where
    for<'a> &'a C: IntoIterator,
    for<'a> <&'a C as IntoIterator>::Item: Display,
{
    /// Format the joined collection, by writing out each element of the
    /// collection, separated by the separator.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut iter = self.collection.into_iter();

        match iter.next() {
            None => Ok(()),
            Some(first) => {
                first.fmt(f)?;

                iter.try_for_each(move |element| {
                    self.sep.fmt(f)?;
                    element.fmt(f)
                })
            }
        }
    }
}

impl<C: IntoIterator, S: Clone> IntoIterator for Join<C, S> {
    type IntoIter = JoinIter<C::IntoIter, S>;
    type Item = JoinItem<C::Item, S>;

    /// Create a consuming iterator from a `Join`. This iterator consumes the
    /// elements of the underlying collection, and intersperses them with clones
    /// of the separator. See the [`JoinIter`] documentation for more details.
    fn into_iter(self) -> Self::IntoIter {
        self.collection.into_iter().iter_join_with(self.sep)
    }
}

impl<'a, C, S> IntoIterator for &'a Join<C, S>
where
    &'a C: IntoIterator,
{
    type IntoIter = JoinIter<<&'a C as IntoIterator>::IntoIter, &'a S>;
    type Item = JoinItem<<&'a C as IntoIterator>::Item, &'a S>;

    /// Create a referential iterator over the join. This iterator iterates
    /// over references to the underlying collection, interspersed with references
    /// to the separator. See the [`JoinIter`] documentation for more details.
    fn into_iter(self) -> Self::IntoIter {
        self.collection.into_iter().iter_join_with(&self.sep)
    }
}

#[cfg(feature = "token-stream")]
impl<C, S> ToTokens for Join<C, S>
where
    for<'a> &'a C: IntoIterator,
    for<'a> <&'a C as IntoIterator>::Item: ToTokens,
    S: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let mut iter = self.collection.into_iter();
        if let Some(first) = iter.next() {
            first.to_tokens(tokens);

            iter.for_each(move |item| {
                self.sep.to_tokens(tokens);
                item.to_tokens(tokens);
            })
        }
    }
}

#[cfg(test)]
mod tests {

    use super::{Joinable, Separator};

    #[test]
    fn empty() {
        let data: Vec<String> = Vec::new();
        let join = data.join_with(", ");
        let result = join.to_string();

        assert_eq!(result, "");
    }

    #[test]
    fn single() {
        let data = vec!["Hello"];
        let join = data.join_with(", ");
        let result = join.to_string();

        assert_eq!(result, "Hello");
    }

    #[test]
    fn simple_join() {
        let data = vec!["This", "is", "a", "sentence"];
        let join = data.join_with(' ');
        let result = join.to_string();

        assert_eq!(result, "This is a sentence");
    }

    #[test]
    fn join_via_separator() {
        let data = vec!["This", "is", "a", "sentence"];
        let join = ' '.separate(data);
        let result = join.to_string();

        assert_eq!(result, "This is a sentence");
    }

    #[test]
    fn iter() {
        use crate::iter::JoinItem;

        let data = vec!["Hello", "World"];
        let join = data.join_with(' ');
        let mut iter = join.into_iter();

        assert_eq!(iter.next(), Some(JoinItem::Element("Hello")));
        assert_eq!(iter.next(), Some(JoinItem::Separator(' ')));
        assert_eq!(iter.next(), Some(JoinItem::Element("World")));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn ref_iter() {
        use crate::iter::JoinItem;

        let data = vec!["Hello", "World"];
        let join = data.join_with(' ');
        let mut iter = (&join).into_iter();

        assert_eq!(iter.next(), Some(JoinItem::Element(&"Hello")));
        assert_eq!(iter.next(), Some(JoinItem::Separator(&' ')));
        assert_eq!(iter.next(), Some(JoinItem::Element(&"World")));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[cfg(feature = "token-stream")]
    #[test]
    fn to_tokens() {
        use crate::separators::NoSeparator;
        use quote::quote;

        let functions = vec![
            quote! {
                fn test1() {}
            },
            quote! {
                fn test2() {}
            },
        ];
        let join = functions.join_with(NoSeparator);

        let result = quote! { #join };
        let target = quote! {
            fn test1() {}
            fn test2() {}
        };

        assert_eq!(result.to_string(), target.to_string());
    }
}
