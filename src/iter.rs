//! Joinery iterator and related types and traits

use core::{
    fmt::{self, Debug, Display, Formatter},
    iter::FusedIterator,
    mem,
};

#[cfg(feature = "nightly")]
use core::{iter::TrustedLen, ops::Try};

use crate::{
    join::{Join, Joinable},
    separators::NoSeparator,
};

/// Specialized helper struct to allow adapting any [`Iterator`] into a [`Join`].
///
/// [`Join`] requires the underlying object to be `&T: IntoIterator`, so that
/// it can be iterated over when formatting via [`Display`]. This works fine for
/// collection types like [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html),
/// but it doesn't work for arbitrary iterators. However, because many iterators
/// are cheaply clonable (because they often just contain a reference to the
/// underlying sequence), we can use this adapter to create an `&T: IntoIterator`
/// type which can be displayed by `Join`.
#[derive(Debug, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct CloneIterator<I>(I);

impl<I: Iterator> IntoIterator for CloneIterator<I> {
    type IntoIter = I;
    type Item = I::Item;

    /// Convert the adapter back into the underlying iterator.
    fn into_iter(self) -> Self::IntoIter {
        self.0
    }
}

impl<'a, I: Iterator + Clone> IntoIterator for &'a CloneIterator<I> {
    type IntoIter = I;
    type Item = I::Item;

    /// Create a referential iterator by cloning the underlying iterator. Note
    /// that this will have the same `Item` type as the underlying iterator,
    /// rather than references to those items.
    fn into_iter(self) -> Self::IntoIter {
        self.0.clone()
    }
}

/// A trait for converting [`Iterator`]s into [`Join`] instances or [`JoinIter`]
/// iterators.
///
/// This trait serves the same purpose as [`Joinable`], but is implemented for `Iterator`
/// types. The main difference between [`JoinableIterator`] and [`Joinable`] is that,
/// because iterators generally don't implement `&T: IntoIterator`, we need a different
/// mechanism to allow for immutably iterating (which is required for [`Join`]'s implementation
/// of [`Display`]).
pub trait JoinableIterator: Iterator + Sized {
    /// Convert a cloneable iterator into a [`Join`] instance. Whenever the [`Join`]
    /// needs to immutabley iterate over the underlying iterator (for instance, when
    /// formatting it with [`Display`]), the underlying iterator is cloned. For most
    /// iterator types this is a cheap operation, because the iterator contains just
    /// a reference to the underlying collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::JoinableIterator;
    ///
    /// let result = (0..4).map(|x| x * 2).join_with(", ").to_string();
    ///
    /// assert_eq!(result, "0, 2, 4, 6");
    /// ```
    fn join_with<S>(self, sep: S) -> Join<CloneIterator<Self>, S>
    where
        Self: Clone,
    {
        CloneIterator(self).join_with(sep)
    }

    /// Convert a [cloneable][Clone] iterator into a [`Join`] instance with no separator.
    /// When formatted with [`Display`], the elements of the iterator will be directly
    /// concatenated.
    /// # Examples
    ///
    /// ```
    /// use joinery::JoinableIterator;
    ///
    /// let result = (0..4).map(|x| x * 2).join_concat().to_string();
    ///
    /// assert_eq!(result, "0246");
    /// ```
    fn join_concat(self) -> Join<CloneIterator<Self>, NoSeparator>
    where
        Self: Clone,
    {
        self.join_with(NoSeparator)
    }

    /// Create an iterator which interspeses the elements of this iterator with
    /// a separator. See [`JoinIter`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use joinery::{JoinableIterator, JoinItem};
    ///
    /// let mut iter = (0..3).map(|x| x * 2).iter_join_with(", ");
    ///
    /// assert_eq!(iter.next(), Some(JoinItem::Element(0)));
    /// assert_eq!(iter.next(), Some(JoinItem::Separator(", ")));
    /// assert_eq!(iter.next(), Some(JoinItem::Element(2)));
    /// assert_eq!(iter.next(), Some(JoinItem::Separator(", ")));
    /// assert_eq!(iter.next(), Some(JoinItem::Element(4)));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn iter_join_with<S>(self, sep: S) -> JoinIter<Self, S> {
        JoinIter::new(self, sep)
    }
}

impl<T: Iterator> JoinableIterator for T {}

/// Enum representing the elements of a [`JoinIter`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum JoinItem<T, S> {
    /// An element from the underlying iterator
    Element(T),
    /// A separator between two elements
    Separator(S),
}

impl<T, S> JoinItem<T, S> {
    /// Convert a [`JoinItem`] into a common type `R`, in the case where both
    /// `T` and `S` can be converted to `R`. Unfortunately, due to potentially
    /// conflicting implementations, we can't implement [`Into<R>`][Into] for
    /// [`JoinItem`].
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

impl<R, T: AsRef<R>, S: AsRef<R>> AsRef<R> for JoinItem<T, S> {
    /// Get a reference to a common type `R` from a [`JoinItem`], in the case where
    /// both `T` and `S` implement [`AsRef<R>`][AsRef]
    fn as_ref(&self) -> &R {
        match self {
            JoinItem::Element(el) => el.as_ref(),
            JoinItem::Separator(sep) => sep.as_ref(),
        }
    }
}

impl<R, T: AsMut<R>, S: AsMut<R>> AsMut<R> for JoinItem<T, S> {
    /// Get a mutable reference to a common type `R` from a [`JoinItem`], in the
    /// case where both `T` and `S` implement [`AsMut<R>`][AsMut]
    fn as_mut(&mut self) -> &mut R {
        match self {
            JoinItem::Element(el) => el.as_mut(),
            JoinItem::Separator(sep) => sep.as_mut(),
        }
    }
}

impl<T: Display, S: Display> Display for JoinItem<T, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            JoinItem::Element(el) => el.fmt(f),
            JoinItem::Separator(sep) => sep.fmt(f),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum JoinIterState<T> {
    /// Unconditionally yield the first item from the inner iterator
    Initial,

    /// Yield a separator if there's an item in the inner iterator
    Separator,

    /// We got an item from the iterator and yielded a separator, so yield
    /// an item
    Element(T),
}

/// An iterator for a [`Join`].
///
/// Emits the elements of the [`Join`]'s underlying iterator, interspersed with
/// its separator. Note that it uses [`clone`][Clone::clone] to generate copies
/// of the separator while iterating, but also keep in mind that in most cases
/// the [`JoinItem`] instance will have a trivially cloneable separator, such
/// as [`&`](https://doc.rust-lang.org/std/primitive.reference.html)[`str`][str]
/// or [`char`].
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
/// Via [`iter_join_with`][JoinableIterator::iter_join_with]:
///
/// ```
/// use joinery::{JoinableIterator, JoinItem};
///
/// let mut iter = (0..6)
///     .filter(|x| x % 2 == 0)
///     .map(|x| x * 2)
///     .iter_join_with(", ");
///
/// assert_eq!(iter.next(), Some(JoinItem::Element(0)));
/// assert_eq!(iter.next(), Some(JoinItem::Separator(", ")));
/// assert_eq!(iter.next(), Some(JoinItem::Element(4)));
/// assert_eq!(iter.next(), Some(JoinItem::Separator(", ")));
/// assert_eq!(iter.next(), Some(JoinItem::Element(8)));
/// assert_eq!(iter.next(), None);
/// ```
#[must_use]
pub struct JoinIter<Iter: Iterator, Sep> {
    iter: Iter,
    sep: Sep,
    state: JoinIterState<Iter::Item>,
}

impl<I: Iterator, S> JoinIter<I, S> {
    /// Construct a new [`JoinIter`] using an iterator and a separator
    fn new(iter: I, sep: S) -> Self {
        JoinIter {
            iter,
            sep,
            state: JoinIterState::Initial,
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
    /// use joinery::{JoinableIterator, JoinItem};
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
        matches!(self.state, JoinIterState::Separator)
    }

    /// Get a reference to the separator.
    #[inline]
    pub fn sep(&self) -> &S {
        &self.sep
    }
}

impl<I: Debug + Iterator, S: Debug> Debug for JoinIter<I, S>
where
    I::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("JoinIter")
            .field("iter", &self.iter)
            .field("sep", &self.sep)
            .field("state", &self.state)
            .finish()
    }
}

impl<I: Clone + Iterator, S: Clone> Clone for JoinIter<I, S>
where
    I::Item: Clone, // Needed because we use a peekable iterator
{
    fn clone(&self) -> Self {
        JoinIter {
            iter: self.iter.clone(),
            sep: self.sep.clone(),
            state: self.state.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.iter.clone_from(&source.iter);
        self.sep.clone_from(&source.sep);
        self.state.clone_from(&source.state);
    }
}

/// Get the size of a [`JoinIter`], given the size of the underlying iterator. If
/// next_sep is true, the next element in the [`JoinIter`] will be the separator.
/// Return None in the event of an overflow. This logic is provided as a separate
/// function in the hopes that it will aid compiler optimization, and also with
/// the intention that in the future it will be a `const fn`.
#[inline]
fn join_size<T>(iter_size: usize, state: &JoinIterState<T>) -> Option<usize> {
    match *state {
        JoinIterState::Initial => match iter_size {
            0 => Some(0),
            _ => (iter_size - 1).checked_mul(2)?.checked_add(1),
        },
        JoinIterState::Separator => iter_size.checked_mul(2),
        JoinIterState::Element(..) => iter_size.checked_mul(2)?.checked_add(1),
    }
}

impl<I: Iterator, S: Clone> Iterator for JoinIter<I, S> {
    type Item = JoinItem<I::Item, S>;

    /// Advance to the next item in the Join. This will either be the next
    /// element in the underlying iterator, or a clone of the separator.
    // We tag it inline in the hopes that the compiler can optimize loops into
    // (mostly) branchless versions, similar to `(Join as Display)::fmt`
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match mem::replace(&mut self.state, JoinIterState::Separator) {
            JoinIterState::Initial => self.iter.next().map(JoinItem::Element),
            JoinIterState::Separator => self.iter.next().map(|element| {
                self.state = JoinIterState::Element(element);
                JoinItem::Separator(self.sep.clone())
            }),
            JoinIterState::Element(element) => Some(JoinItem::Element(element)),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min, max) = self.iter.size_hint();

        let min = join_size(min, &self.state).unwrap_or(core::usize::MAX);
        let max = max.and_then(|max| join_size(max, &self.state));

        (min, max)
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        match self.state {
            JoinIterState::Initial => (self.iter.count() * 2).saturating_sub(1),
            JoinIterState::Separator => self.iter.count() * 2,
            JoinIterState::Element(_) => self.iter.count() * 2 + 1,
        }
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.iter
            .last()
            .or(match self.state {
                JoinIterState::Initial | JoinIterState::Separator => None,
                JoinIterState::Element(item) => Some(item),
            })
            .map(JoinItem::Element)
    }

    fn fold<B, F>(mut self, init: B, mut func: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let accum = match self.state {
            JoinIterState::Initial => match self.iter.next() {
                None => return init,
                Some(element) => func(init, JoinItem::Element(element)),
            },
            JoinIterState::Separator => init,
            JoinIterState::Element(element) => func(init, JoinItem::Element(element)),
        };

        self.iter.fold(accum, move |accum, element| {
            let accum = func(accum, JoinItem::Separator(self.sep.clone()));
            func(accum, JoinItem::Element(element))
        })
    }

    #[cfg(feature = "nightly")]
    fn try_fold<B, F, R>(&mut self, init: B, mut func: F) -> R
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        use core::ops::ControlFlow;

        let accum = match mem::replace(&mut self.state, JoinIterState::Separator) {
            JoinIterState::Initial => match self.iter.next() {
                None => return R::from_output(init),
                Some(element) => func(init, JoinItem::Element(element))?,
            },
            JoinIterState::Separator => init,
            JoinIterState::Element(element) => func(init, JoinItem::Element(element))?,
        };

        self.iter.try_fold(accum, |accum, element| {
            match func(accum, JoinItem::Separator(self.sep.clone())).branch() {
                ControlFlow::Break(err) => {
                    self.state = JoinIterState::Element(element);
                    R::from_residual(err)
                }
                ControlFlow::Continue(accum) => func(accum, JoinItem::Element(element)),
            }
        })
    }
}

impl<I: FusedIterator, S: Clone> FusedIterator for JoinIter<I, S> {}

#[cfg(feature = "nightly")]
unsafe impl<I: TrustedLen, S: Clone> TrustedLen for JoinIter<I, S> {}

#[cfg(test)]
mod tests {
    use super::JoinItem::*;
    use super::JoinableIterator;

    #[test]
    fn empty_iter() {
        let mut join_iter = (0..0).iter_join_with(", ");

        assert_eq!(join_iter.next(), None);
        assert_eq!(join_iter.next(), None);
    }

    #[test]
    fn single() {
        let mut join_iter = (0..1).iter_join_with(", ");

        assert_eq!(join_iter.next(), Some(Element(0)));
        assert_eq!(join_iter.next(), None);
        assert_eq!(join_iter.next(), None);
    }

    #[test]
    fn few() {
        let mut join_iter = (0..3).iter_join_with(", ");

        assert_eq!(join_iter.next(), Some(Element(0)));
        assert_eq!(join_iter.next(), Some(Separator(", ")));
        assert_eq!(join_iter.next(), Some(Element(1)));
        assert_eq!(join_iter.next(), Some(Separator(", ")));
        assert_eq!(join_iter.next(), Some(Element(2)));
        assert_eq!(join_iter.next(), None);
        assert_eq!(join_iter.next(), None);
    }

    #[test]
    fn regular_size_hint() {
        let mut join_iter = (0..10).iter_join_with(", ");

        for size in (0..=19).rev() {
            assert_eq!(join_iter.size_hint(), (size, Some(size)));
            join_iter.next();
        }

        assert_eq!(join_iter.size_hint(), (0, Some(0)));
        join_iter.next();
        assert_eq!(join_iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn large_size_hint() {
        let join_iter = (0..usize::max_value() - 10).iter_join_with(", ");
        assert_eq!(join_iter.size_hint(), (usize::max_value(), None));
    }

    #[test]
    fn threshold_size_hint() {
        use core::usize::MAX as usize_max;
        let usize_threshold = (usize_max / 2) + 1;

        let mut join_iter = (0..usize_threshold + 1).iter_join_with(", ");
        assert_eq!(join_iter.size_hint(), (usize_max, None));

        join_iter.next();
        assert_eq!(join_iter.size_hint(), (usize_max, None));

        join_iter.next();
        assert_eq!(join_iter.size_hint(), (usize_max, Some(usize_max)));

        join_iter.next();
        assert_eq!(join_iter.size_hint(), (usize_max - 1, Some(usize_max - 1)));
    }

    #[test]
    fn partial_iteration() {
        use std::vec::Vec;

        let mut join_iter = (0..3).iter_join_with(' ');

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
        let join_iter = content.iter().iter_join_with(4);

        let sum = join_iter.fold(0, |accum, next| match next {
            Element(el) => accum + el,
            Separator(sep) => accum + sep,
        });

        assert_eq!(sum, 14);
    }

    #[test]
    fn partial_fold() {
        let content = [1, 2, 3, 4];
        let mut join_iter = content.iter().iter_join_with(1);

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
        let mut join_iter = content.iter().iter_join_with(1);

        let result = join_iter.try_fold(0, |accum, next| match next {
            Separator(sep) => Ok(accum + sep),
            Element(el) if *el == 0 => Err(accum),
            Element(el) => Ok(accum + el),
        });

        assert_eq!(result, Err(5));
    }

    // This test exists because implementing JoinIter::try_fold in terms of
    // JoinIter.iter::try_fold is non trivial, and the naive (incorrect) implementation
    // fails this test.
    #[test]
    fn partial_try_fold() {
        let content = [1, 2, 3];
        let mut join_iter = content.iter().iter_join_with(1);

        let _ = join_iter.try_fold(1, |_, next| match next {
            Element(_) => Some(1),
            Separator(_) => None,
        });

        // At this point, the remaining elements in the iterator SHOULD be E(2), S(1), E(3)
        assert_eq!(join_iter.count(), 3);
    }

    #[test]
    fn last_empty() {
        let content: [i32; 0] = [];
        let join_iter = content.iter().iter_join_with(0);

        assert_eq!(join_iter.last(), None);
    }

    #[test]
    fn last_only() {
        let content = [1];
        let join_iter = content.iter().iter_join_with(0);

        assert_eq!(join_iter.last(), Some(Element(&1)));
    }

    #[test]
    fn last_initial() {
        let content = [1, 2, 3];
        let join_iter = content.iter().iter_join_with(0);

        assert_eq!(join_iter.last(), Some(Element(&3)));
    }

    #[test]
    fn last_sep() {
        let content = [1, 2, 3];
        let mut join_iter = content.iter().iter_join_with(0);
        join_iter.next().unwrap();

        assert_eq!(join_iter.last(), Some(Element(&3)));
    }

    #[test]
    fn last_element() {
        let content = [1, 2, 3];
        let mut join_iter = content.iter().iter_join_with(0);
        join_iter.next().unwrap();
        join_iter.next().unwrap();

        assert_eq!(join_iter.last(), Some(Element(&3)));
    }

    #[test]
    fn last_sep_2() {
        let content = [1, 2];
        let mut join_iter = content.iter().iter_join_with(0);
        join_iter.next().unwrap();

        assert_eq!(join_iter.last(), Some(Element(&2)));
    }

    #[test]
    fn last_element_2() {
        let content = [1, 2];
        let mut join_iter = content.iter().iter_join_with(0);
        join_iter.next().unwrap();
        join_iter.next().unwrap();

        assert_eq!(join_iter.last(), Some(Element(&2)));
    }

    #[test]
    fn last_emptied() {
        let content = [1, 2];
        let mut join_iter = content.iter().iter_join_with(0);
        join_iter.next().unwrap();
        join_iter.next().unwrap();
        join_iter.next().unwrap();

        assert_eq!(join_iter.last(), None);
    }
}
