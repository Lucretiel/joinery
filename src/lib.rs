#![no_std]
#![cfg_attr(feature = "nightly", feature(trusted_len))]

//! Joinery provides generic joining of iterables with separators. While it is
//! primarily designed the typical use case of writing to a [writer][fmt::Write]
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
//! let result = [1, 2, 3, 4].iter().join_with(", ").to_string();
//! assert_eq!(result, "1, 2, 3, 4")
//! ```
//!
//! Create a newline separated list, using a python-style syntax (with the
//! separator at the beginning of the expression):
//!
//! ```
//! use joinery::Separator;
//!
//! let result = '\n'.separate(&[1, 2, 3]).to_string();
//! assert_eq!(result, "1\n2\n3");
//! ```
//!
//! `write!` a comma-separated list:
//!
//! ```
//! use joinery::Joinable;
//! # use std::fmt::Write;
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
//! Iterate over joins:
//!
//! ```
//! use joinery::{Joinable, JoinItem};
//!
//! // Note that the collection values and the separator can be different types
//! let join = ["some", "sample", "text"].iter().join_with(' ');
//! let mut join_iter = join.iter();
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
//! use joinery::Joinable;
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

#[cfg(test)]
extern crate std;

use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{FusedIterator, Peekable};

#[cfg(feature = "nightly")]
use core::iter::TrustedLen;

/// A trait for converting iterables and collections into [`Join`] instances.
///
/// This trait is the primary way to create [`Join`] instances. It is
/// implemented for all referentially iterable types; that is, for all types
/// for which &T: IntoIterator. See [`join_with`][Joinable::join_with] for an
/// example of its usage.
pub trait Joinable {
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
    fn join_with<S>(self, sep: S) -> Join<Self, S> where Self: Sized;

    /// Join this object an [empty separator](NoSeparator). When rendered
    /// with [`Display`], the underlying elements will be directly concatenated.
    /// Note that the separator, while empty, is still present, and will show
    /// up if you [iterate](Join::iter) this instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::Joinable;
    ///
    /// let parts = vec!['a', 'b', 'c', 'd', 'e'];
    /// let join = parts.iter().join_concat();
    /// assert_eq!(join.to_string(), "abcde");
    /// ```
    ///
    /// *New in 1.1.0*
    fn join_concat(self) -> Join<Self, NoSeparator>
    where
        Self: Sized,
    {
        self.join_with(NoSeparator)
    }
}

impl<T> Joinable for T
    where for <'a> &'a T: IntoIterator
{
    fn join_with<S>(self, sep: S) -> Join<Self, S> {
        Join {
            container: self,
            sep,
        }
    }
}

// NOTE: we hope that the compiler will detect that most operations on NoSeparator
// are no-ops, and optimize heavily, because I'd rather not implement a separate
// type for empty-separator-joins.

/// Zero-size type representing the empty separator.
///
/// This struct can be used as a separator in cases where you simply want to
/// join the elements of a separator without any elements between them.
///
/// See also the [`join_concat`](Joinable::join_concat) method.
///
/// # Examples
///
/// ```
/// use joinery::{Joinable, NoSeparator};
///
/// let parts = (0..10);
/// let join = parts.join_with(NoSeparator);
/// assert_eq!(join.to_string(), "0123456789");
/// ```
///
/// *New in 1.1.0*
#[derive(Debug, Clone, Copy, Default)]
pub struct NoSeparator;

impl Display for NoSeparator {
    #[inline(always)]
    fn fmt(&self, _f: &mut Formatter) -> fmt::Result {
        Ok(())
    }
}

/// A trait for using a separator to produce a [`Join`].
///
/// This trait provides a more python-style interface for performing joins.
/// Rather than do [`collection.join_with`][Joinable::join_with], you do:
///
/// ```
/// use joinery::Separator;
///
/// let join = ", ".separate(&[1, 2, 3, 4]);
/// assert_eq!(join.to_string(), "1, 2, 3, 4");
/// ```
///
/// By default, [`Separator`] is implemented for [`char`], [`&str`][str], and
/// [`NoSeparator`].
///
/// Note that any type can be used as a separator in a [`Join`] when
/// creating one via [`Joinable::join_with`]. The [`Separator`] trait and its
/// implementations on [`char`] and [`&str`][str] are provided simply as
/// a convenience.
pub trait Separator {
    /// Combine a [`Separator`] with a [`Joinable`] to create a [`Join`].
    fn separate<T: Joinable>(self, container: T) -> Join<T, Self>
        where Self: Sized
    {
        container.join_with(self)
    }
}

impl<'a> Separator for &'a str {}
impl Separator for char {}
impl Separator for NoSeparator {}

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
}

impl<C, S: Display> Display for Join<C, S>
where
    for <'a> &'a C: IntoIterator,
    for <'a> <&'a C as IntoIterator>::Item: Display,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let iter = self.container.into_iter();

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
        JoinIter::new(self.container.into_iter(), self.sep)
    }
}

impl<'a, C, S> IntoIterator for &'a Join<C, S>
    where &'a C: IntoIterator
{
    type IntoIter = JoinIter<<&'a C as IntoIterator>::IntoIter, &'a S>;
    type Item = JoinItem<<&'a C as IntoIterator>::Item, &'a S>;

    fn into_iter(self) -> Self::IntoIter {
        JoinIter::new(self.container.into_iter(), &self.sep)
    }
}

impl<'a, C, S> IntoIterator for &'a mut Join<C, S>
    where &'a mut C: IntoIterator
{
    type IntoIter = JoinIter<<&'a mut C as IntoIterator>::IntoIter, &'a S>;
    type Item = JoinItem<<&'a mut C as IntoIterator>::Item, &'a S>;

    fn into_iter(self) -> Self::IntoIter {
        JoinIter::new(self.container.into_iter(), &self.sep)
    }
}

impl<C, S> Join<C, S>
{
    pub fn iter(&self) -> JoinIter<<&C as IntoIterator>::IntoIter, &S>
        where for <'a> &'a C: IntoIterator
    {
        self.into_iter()
    }

    pub fn iter_mut(&mut self) -> JoinIter<<&mut C as IntoIterator>::IntoIter, &S>
        where for<'a> &'a mut C: IntoIterator
    {
        self.into_iter()
    }
}

/// Enum representing the elements of a [`JoinIter`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JoinItem<T, S> {
    /// An element from the underlying iterator
    Element(T),
    /// A separator between two elements
    Separator(S),
}

impl<T, S> JoinItem<T, S> {
    /// Convert a [`JoinItem`] into a common type `R`, in the case where both
    /// `T` and `S` can be converted to `R`. Unfortunately, due to potentially
    /// conflicting implementations, we can't implement `Into<R>` for `JoinItem`.
    pub fn into<R>(self) -> R
    where
        T: Into<R>,
        S: Into<R>,
    {
        match self {
            JoinItem::Element(el) => el.into(),
            JoinItem::Separator(sep) => sep.into(),
        }
    }
}

/// Get a reference to a common type `R` from a [`JoinItem`], in the case where
/// both `T` and `S` implement [`AsRef<R>`][AsRef]
impl<R, T: AsRef<R>, S: AsRef<R>> AsRef<R> for JoinItem<T, S> {
    fn as_ref(&self) -> &R {
        match self {
            JoinItem::Element(el) => el.as_ref(),
            JoinItem::Separator(sep) => sep.as_ref(),
        }
    }
}

impl<T: Display, S: Display> Display for JoinItem<T, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use JoinItem::*;

        match self {
            Element(el) => el.fmt(f),
            Separator(sep) => sep.fmt(f),
        }
    }
}

/// An iterator for a [`Join`].
///
/// Emits the elements of the [`Join`]'s underlying iterator, interspersed with
/// its separator. Note that it uses [`clone`][Clone::clone] to generate copies
/// of the separator while iterating, but also keep in mind that in most cases
/// the [`JoinItem`] instance will have a trivially cloneable reference to the
/// separator, rather than the separator itself.
///
/// # Examples
///
/// Via [`IntoIterator`]:
///
/// ```
/// use joinery::{Joinable, JoinItem};
///
/// let join = vec![1, 2, 3].join_with(" ");
/// let mut join_iter = join.into_iter();
///
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(1)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(" ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(2)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(" ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(3)));
/// assert_eq!(join_iter.next(), None);
/// ```
///
/// Via [`.iter()`][Join::iter]
///
/// ```
/// use joinery::{Joinable, JoinItem};
///
/// let join = vec![1, 2, 3].join_with(" ");
/// let mut join_iter = join.iter();
///
/// // Note that using .iter() produces references to the separator, rather than clones.
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(1)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(&" ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(2)));
/// assert_eq!(join_iter.next(), Some(JoinItem::Separator(&" ")));
/// assert_eq!(join_iter.next(), Some(JoinItem::Element(3)));
/// assert_eq!(join_iter.next(), None);
/// ```
pub struct JoinIter<Iter: Iterator, Sep> {
    iter: Peekable<Iter>,
    sep: Sep,
    next_sep: bool,
}

impl<I: Iterator, S> JoinIter<I, S> {
    fn new(iter: I, sep: S) -> Self {
        JoinIter {
            iter: iter.peekable(),
            sep,
            next_sep: false,
        }
    }
}

impl<I: Iterator, S> JoinIter<I, S> {
    /// Check if the next iteration of this iterator will (try to) return a
    /// separator. Note that this does not check if the underlying iterator is
    /// empty, so the next `next` call could still return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::{Joinable, JoinItem};
    ///
    /// let mut join_iter = (0..3).join_with(", ").into_iter();
    ///
    /// assert_eq!(join_iter.is_sep_next(), false);
    /// join_iter.next();
    /// assert_eq!(join_iter.is_sep_next(), true);
    /// join_iter.next();
    /// assert_eq!(join_iter.is_sep_next(), false);
    /// ```
    #[inline]
    pub fn is_sep_next(&self) -> bool {
        self.next_sep
    }

    /// Get a reference to the separator.
    #[inline]
    pub fn sep(&self) -> &S {
        &self.sep
    }

    /// Peek at what the next item in the iterator will be without consuming
    /// it. Note that this interface is similar, but not identical, to
    /// [`Peekable::peek`].
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::{Joinable, JoinItem};
    ///
    /// let mut join_iter = (0..3).join_with(", ").into_iter();
    ///
    /// assert_eq!(join_iter.peek(), Some(JoinItem::Element(&0)));
    /// assert_eq!(join_iter.next(), Some(JoinItem::Element(0)));
    /// assert_eq!(join_iter.peek(), Some(JoinItem::Separator(&", ")));
    /// assert_eq!(join_iter.next(), Some(JoinItem::Separator(", ")));
    /// assert_eq!(join_iter.peek(), Some(JoinItem::Element(&1)));
    /// assert_eq!(join_iter.next(), Some(JoinItem::Element(1)));
    /// ```
    pub fn peek(&mut self) -> Option<JoinItem<&I::Item, &S>> {
        let next_sep = self.next_sep;
        let sep = &self.sep;

        self.iter.peek().map(move |element| {
            if next_sep {
                JoinItem::Separator(sep)
            } else {
                JoinItem::Element(element)
            }
        })
    }

    /// Peek at what the next non-separator item in the iterator will be
    /// without consuming it.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::{Joinable, JoinItem};
    ///
    /// let mut join_iter = vec!["This", "is", "a", "sentence"].join_with(' ').into_iter();
    ///
    /// assert_eq!(join_iter.peek_element(), Some(&"This"));
    /// assert_eq!(join_iter.peek(), Some(JoinItem::Element(&"This")));
    /// assert_eq!(join_iter.next(), Some(JoinItem::Element("This")));
    ///
    /// assert_eq!(join_iter.peek_element(), Some(&"is"));
    /// assert_eq!(join_iter.peek(), Some(JoinItem::Separator(&' ')));
    /// assert_eq!(join_iter.next(), Some(JoinItem::Separator(' ')));
    ///
    /// assert_eq!(join_iter.peek_element(), Some(&"is"));
    /// assert_eq!(join_iter.peek(), Some(JoinItem::Element(&"is")));
    /// assert_eq!(join_iter.next(), Some(JoinItem::Element("is")));
    /// ```
    pub fn peek_element(&mut self) -> Option<&I::Item> {
        self.iter.peek()
    }
}

impl<I, S> Debug for JoinIter<I, S>
where
    I: Iterator + Debug,
    S: Debug,
    I::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("JoinIter")
            .field("iter", &self.iter)
            .field("sep", &self.sep)
            .field("next_sep", &self.next_sep)
            .finish()
    }
}

impl<I: Iterator, S> From<Join<I, S>> for JoinIter<I, S> {
    fn from(join: Join<I, S>) -> Self {
        JoinIter {
            iter: join.iter.peekable(),
            sep: join.sep,
            next_sep: false,
        }
    }
}

impl<I, S> Clone for JoinIter<I, S>
where
    I: Iterator + Clone,
    S: Clone,
    I::Item: Clone, // Needed because we use a peekable iterator
{
    fn clone(&self) -> Self {
        JoinIter {
            iter: self.iter.clone(),
            sep: self.sep.clone(),
            next_sep: self.next_sep,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.iter.clone_from(&source.iter);
        self.sep.clone_from(&source.sep);
        self.next_sep = source.next_sep;
    }
}

impl<I: Iterator, S: Clone> JoinIter<I, S> {
    /// Convert the [`JoinItem`] elements of a [`JoinIter`] into some common
    /// type, using [`Into`] The type should be one that both the iterator items
    /// and the separator can be converted into via [`Into`]. Note that, because
    /// [`Into`] is reflexive, this can be used in cases where the separator and
    /// the item are the same type.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::Joinable;
    ///
    /// // Use this function to aid with type inference
    /// fn assert_str(lhs: Option<&str>, rhs: Option<&str>) {
    ///     assert_eq!(lhs, rhs);
    /// }
    ///
    /// let content = vec!["Hello", "World!"];
    ///
    /// let join = content.join_with(", ");
    /// let mut iter = join.into_iter().normalize();
    ///
    /// assert_str(iter.next(), Some("Hello"));
    /// assert_str(iter.next(), Some(", "));
    /// assert_str(iter.next(), Some("World!"));
    /// assert_str(iter.next(), None);
    ///
    ///
    /// ```
    pub fn normalize<R>(self) -> impl Iterator<Item = R>
    where
        I::Item: Into<R>,
        S: Into<R>,
    {
        self.map(|item| item.into())
    }
}

/// Get the size of a [`JoinIter`], given the size of the underlying iterator. If
/// next_sep is true, the next element in the [`JoinIter`] will be the separator.
/// Return None in the event of an overflow. This logic is provided as a separate
/// function in the hopes that it will aid compiler optimization, and also with
/// the intention that in the future it will be a `const fn`.
#[inline]
fn join_size(iter_size: usize, next_sep: bool) -> Option<usize> {
    if iter_size == 0 {
        Some(0)
    } else if next_sep {
        iter_size.checked_mul(2)
    } else {
        // TODO: this might be faster with wrapping operations and explicit checks
        // Interestingly, I'm pretty sure that if checked_mul didn't overflow, then
        // the +1 is also guarenteed to not overflow.
        (iter_size - 1).checked_mul(2).map(|val| val + 1)
    }
}

impl<I: Iterator, S: Clone> Iterator for JoinIter<I, S> {
    type Item = JoinItem<I::Item, S>;

    /// Advance to the next item in the Join. This will either be the next
    /// element in the underlying iterator, or a clone of the separator.
    fn next(&mut self) -> Option<Self::Item> {
        let sep = &self.sep;
        let next_sep = &mut self.next_sep;

        if *next_sep {
            self.iter.peek().map(|_| {
                *next_sep = false;
                JoinItem::Separator(sep.clone())
            })
        } else {
            self.iter.next().map(|element| {
                *next_sep = true;
                JoinItem::Element(element)
            })
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min, max) = self.iter.size_hint();

        let min = join_size(min, self.next_sep).unwrap_or(usize::max_value());
        let max = max.and_then(|max| join_size(max, self.next_sep));

        (min, max)
    }

    fn fold<B, F>(self, init: B, mut func: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let mut iter = self.iter.map(JoinItem::Element);
        let sep = self.sep;

        let accum = if !self.next_sep {
            match iter.next() {
                None => return init,
                Some(element) => func(init, element),
            }
        } else {
            init
        };

        iter.fold(accum, move |accum, element| {
            let accum = func(accum, JoinItem::Separator(sep.clone()));
            func(accum, element)
        })
    }

    // TODO: Add try_fold implementation based on self.iter.try_fold.
    // Unfortunately, this will be difficult, because when the reducer is called,
    // it has to make a decision about if and when to evaluate the separator.
}

impl<I: FusedIterator, S: Clone> FusedIterator for JoinIter<I, S> {}

#[cfg(feature = "nightly")]
unsafe impl<I: TrustedLen, S: Clone> TrustedLen for JoinIter<I, S> {}

/// The joinery prelude
pub mod prelude {
    pub use {Joinable, Separator};
}

#[cfg(test)]
mod tests {
    use std::string::ToString;

    macro_rules! join_test {
        ($($test:ident : ($content:expr) @ $join:tt => $expected:expr);*) => {$(
            #[test]
            fn $test() {
                use std::string::ToString;
                use {Joinable, Separator};

                let content = $content;
                let result = content.join_with($join).to_string();
                assert_eq!(result, $expected);

                let content = $content;
                let result = $join.separate(content.into_iter()).to_string();
                assert_eq!(result, $expected);
            }
        )*};
    }

    join_test!{
        join_empty: (0..0) @ ", " => "";
        join_one: (["Hello, World"]) @ ":::" => "Hello, World";
        string_join_char: (["This", "is", "a", "sentence"]) @ ' ' => "This is a sentence";
        char_join_string: (['a', 'b', 'c', 'd', 'e']) @ ", " => "a, b, c, d, e";
        range_join: (0..5) @ ", " => "0, 1, 2, 3, 4"
    }

    #[test]
    fn lines() {
        use {Joinable, Separator};

        let lines = [
            ["This", "is", "line", "1"],
            ["This", "is", "line", "2"],
            ["This", "is", "line", "3"],
        ];

        let result = lines
            .iter()
            .map(|line| ", ".separate(line))
            .join_with('\n')
            .to_string();
        assert_eq!(
            result,
            "This, is, line, 1\n\
             This, is, line, 2\n\
             This, is, line, 3"
        );
    }

    #[test]
    fn counting() {
        use Joinable;

        let result = (1..=5)
            .map(|m| (0..5).map(move |n| n * m).join_with(", "))
            .join_with("\n")
            .to_string();

        assert_eq!(
            result,
            "0, 1, 2, 3, 4\n\
             0, 2, 4, 6, 8\n\
             0, 3, 6, 9, 12\n\
             0, 4, 8, 12, 16\n\
             0, 5, 10, 15, 20"
        );
    }

    #[test]
    fn join_size() {
        use super::join_size;
        use std::usize::MAX as usize_max;

        assert_eq!(join_size(0, true), Some(0));
        assert_eq!(join_size(0, false), Some(0));

        assert_eq!(join_size(12, true), Some(24));
        assert_eq!(join_size(12, false), Some(23));

        assert_eq!(join_size(usize_max, true), None);
        assert_eq!(join_size(usize_max, false), None);
    }

    mod iter {
        use JoinItem::*;
        use Joinable;

        #[test]
        fn empty_iter() {
            let mut join_iter = (0..0).join_with(", ").into_iter();

            assert_eq!(join_iter.next(), None);
        }

        #[test]
        fn single() {
            let mut join_iter = (0..1).join_with(", ").into_iter();

            assert_eq!(join_iter.next(), Some(Element(0)));
            assert_eq!(join_iter.next(), None);
        }

        #[test]
        fn few() {
            let mut join_iter = (0..3).join_with(", ").into_iter();

            assert_eq!(join_iter.next(), Some(Element(0)));
            assert_eq!(join_iter.next(), Some(Separator(", ")));
            assert_eq!(join_iter.next(), Some(Element(1)));
            assert_eq!(join_iter.next(), Some(Separator(", ")));
            assert_eq!(join_iter.next(), Some(Element(2)));
            assert_eq!(join_iter.next(), None);
        }

        #[test]
        fn regular_size_hint() {
            let mut join_iter = (0..10).join_with(", ").into_iter();
            assert_eq!(join_iter.size_hint(), (19, Some(19)));

            join_iter.next();
            assert_eq!(join_iter.size_hint(), (18, Some(18)));
        }

        #[test]
        fn large_size_hint() {
            let join_iter = (0..usize::max_value() - 10).join_with(", ").into_iter();
            assert_eq!(join_iter.size_hint(), (usize::max_value(), None));
        }

        #[test]
        fn threshold_size_hint() {
            let umax = usize::max_value();
            let usize_threshold = (usize::max_value() / 2) + 1;

            let mut join_iter = (0..usize_threshold + 1).join_with(", ").into_iter();
            assert_eq!(join_iter.size_hint(), (umax, None));

            join_iter.next();
            assert_eq!(join_iter.size_hint(), (umax, None));

            join_iter.next();
            assert_eq!(join_iter.size_hint(), (umax, Some(umax)));
        }

        #[test]
        fn test_partial_iteration() {
            use std::vec::Vec;

            let content = 0..3;
            let mut join_iter = content.join_with(' ').into_iter();

            join_iter.next();

            let rest: Vec<_> = join_iter.collect();
            assert_eq!(
                rest,
                [Separator(' '), Element(1), Separator(' '), Element(2),]
            );
        }

        #[test]
        fn fold() {
            let content = [1, 2, 3];
            let join_iter = content.iter().join_with(4).into_iter();

            let sum = join_iter.fold(0, |accum, next| match next {
                Element(el) => accum + el,
                Separator(sep) => accum + sep,
            });

            assert_eq!(sum, 14);
        }

        #[test]
        fn partial_fold() {
            let content = [1, 2, 3, 4];
            let mut join_iter = content.iter().join_with(1).into_iter();

            join_iter.next();
            join_iter.next();
            join_iter.next();

            let sum = join_iter.fold(0, |accum, next| match next {
                Element(el) => accum + el,
                Separator(sep) => accum + sep,
            });

            assert_eq!(sum, 9);
        }

        #[test]
        fn try_fold() {
            let content = [1, 2, 0, 3];
            let mut join_iter = content.iter().join_with(1).into_iter();

            let result = join_iter.try_fold(0, |accum, next| match next {
                Separator(sep) => Ok(accum + sep),
                Element(el) if *el == 0 => Err(accum),
                Element(el) => Ok(accum + el),
            });

            assert_eq!(result, Err(5));
        }

        #[test]
        fn partial_try_fold() {
            let content = [1, 2, 3];
            let mut join_iter = content.iter().join_with(1).into_iter();

            let _ = join_iter.try_fold(1, |_, next| match next {
                Element(_) => Some(1),
                Separator(_) => None,
            });

            // At this point, the remaining elements in the iterator SHOULD be E(2), S(1), E(3)
            assert_eq!(join_iter.count(), 3);
        }
    }
}
