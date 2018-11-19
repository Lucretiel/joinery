//! The primary join types

use core::fmt::{self, Display, Formatter};

use crate::iter::{JoinableIterator, JoinItem, JoinIter};
use crate::separators::NoSeparator;

/// A trait for converting collections into [`Join`] instances.
///
/// This trait is implemented for all referentially iterable types; that is,
/// for all types for which &T: IntoIterator. See [`join_with`][Joinable::join_with]
/// for an example of its usage.
pub trait Joinable: Sized {
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
    fn join_with<S>(self, sep: S) -> Join<Self, S>;

    fn join_concat(self) -> Join<Self, NoSeparator> {
        self.join_with(NoSeparator)
    }
}

impl<T> Joinable for T
where
    for<'a> &'a T: IntoIterator,
{
    fn join_with<S>(self, sep: S) -> Join<Self, S> {
        Join {
            container: self,
            sep,
        }
    }
}

pub trait Separator: Sized {
    fn separate<T: Joinable>(self, container: T) -> Join<T, Self> {
        container.join_with(self)
    }
}

impl Separator for char {}
impl<'a> Separator for &'a str {}

/// The primary data structure for representing a joined sequence.
///
/// It contains an interator and a separator, and represents the elements of the
/// iterator with the separator dividing each element.
///
/// A [`Join`] is created with [`Joinable::join_with`] or [`Separator::separate`].
/// It can be [iterated][Join::iter], and implements [`Display`] so that it can
/// be written to a [writer][fmt::Write] or converted into a `String`.
///
///
/// # Examples
///
/// Writing via [`Display`]:
///
/// ```
/// use joinery::Joinable;
/// use std::fmt::Write;
///
/// let content = 0..10;
/// let join = content.join_with(", ");
///
/// let mut buffer = String::new();
/// write!(buffer, "Numbers: {}", join);
///
/// assert_eq!(buffer, "Numbers: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9");
///
/// // Don't forget that `Display` gives to `ToString` for free!
/// assert_eq!(join.to_string(), "0, 1, 2, 3, 4, 5, 6, 7, 8, 9")
/// ```
///
/// Iterating via [`IntoIterator`]:
///
/// ```
/// use joinery::{Separator, JoinItem};
///
/// let content = 0..3;
/// let join = ", ".separate(content);
/// let mut join_iter = join.into_iter();
///
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(0)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(", ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(1)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(", ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(2)));
/// assert_eq!(join_iter.next(), None);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct Join<Container, Sep> {
    container: Container,
    sep: Sep,
}

impl<C, S> Join<C, S> {
    /// Get a reference to the separator.
    pub fn sep(&self) -> &S {
        &self.sep
    }
    /// Get a reference to the underlying container.
    pub fn container(&self) -> &C {
        &self.container
    }

    pub fn into_inner(self) -> C {
        self.container
    }
    /// Consume `self` and return the separator and underlying iterator.
    pub fn into_parts(self) -> (C, S) {
        (self.container, self.sep)
    }

    pub fn iter(&self) -> JoinIter<<&C as IntoIterator>::IntoIter, &S>
        where for <'a> &'a C: IntoIterator
    {
        self.into_iter()
    }
}

mod private {
    use core::fmt;
    pub trait Display<'a>: fmt::Display {}
    impl<'a, T: fmt::Display> Display<'a> for T {}
}

impl<C, S> Display for Join<C, S>
where
    for<'a> &'a C: IntoIterator,
    for<'a> <&'a C as IntoIterator>::Item: private::Display<'a>,
    S: Display,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut iter = self.container.into_iter();

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

    fn into_iter(self) -> Self::IntoIter {
        self.container.into_iter().iter_join_with(self.sep)
    }
}

impl<'a, C, S> IntoIterator for &'a Join<C, S>
where
    &'a C: IntoIterator,
{
    type IntoIter = JoinIter<<&'a C as IntoIterator>::IntoIter, &'a S>;
    type Item = JoinItem<<&'a C as IntoIterator>::Item, &'a S>;

    fn into_iter(self) -> Self::IntoIter {
        self.container.into_iter().iter_join_with(&self.sep)
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
}
