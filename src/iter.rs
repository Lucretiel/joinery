use core::fmt::{self, Display, Formatter, Debug};
use core::iter::{Peekable, FusedIterator};

#[cfg(feature = "nightly")]
use core::iter::TrustedLen;

use crate::join::{Join, Joinable};
use crate::separators::NoSeparator;

/// Specialized helper struct to allow adapting any [`Iterator`] into a [`Join`].
/// [`Join`] requires the underlying object to be `&T: IntoIterator`, so that
/// it can be iterated over when formatting via [`Display`]. This works fine for
/// container types like [`Vec`], but it doesn't work for arbitrary iterators.
/// However, because many iterators are cheaply clonable (because they often
/// just contain a reference to the underlying sequence), we can use this adapter
/// to create an `IntoIterator` type which can be displayed by `Join`.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CloneIterator<I> {
    iter: I,
}

impl<'a, I: Iterator + Clone> IntoIterator for &'a CloneIterator<I> {
    type IntoIter = I;
    type Item = I::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.clone()
    }
}

impl<I: Iterator> IntoIterator for CloneIterator<I> {
    type IntoIter = I;
    type Item = I::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

pub trait JoinableIterator: Iterator + Sized {
    fn join_with<S>(self, sep: S) -> Join<CloneIterator<Self>, S>
    where Self: Clone,
    {
        CloneIterator { iter: self }.join_with(sep)
    }

    fn join_concat(self) -> Join<CloneIterator<Self>, NoSeparator>
        where Self: Clone,
    {
        self.join_with(NoSeparator)
    }

    fn iter_join_with<S>(self, sep: S) -> JoinIter<Self, S>
    {
        JoinIter::new(self, sep)
    }
}

impl<T: Iterator> JoinableIterator for T {}

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

impl<R, T: AsMut<R>, S: AsMut<R>> AsMut<R> for JoinItem<T, S> {
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
        let sep = &self.sep;
        let next_sep = self.next_sep;

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

impl<I: Debug, S: Debug> Debug for JoinIter<I, S>
where
    I: Iterator,
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
        // Interestingly, If checked_mul didn't overflow, then the +1 is also
        // guarenteed to not overflow.
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

        let min = join_size(min, self.next_sep).unwrap_or(core::usize::MAX);
        let max = max.and_then(|max| join_size(max, self.next_sep));

        (min, max)
    }

    fn fold<B, F>(self, init: B, mut func: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        let mut iter = self.iter.map(JoinItem::Element);
        let sep = self.sep;

        let accum = if self.next_sep {
            init
        } else {
            match iter.next() {
                None => return init,
                Some(element) => func(init, element),
            }
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

#[cfg(test)]
mod tests {
    use super::JoinItem::*;
    use super::JoinableIterator;

    #[test]
    fn join_size() {
        use super::join_size;
        use core::usize::MAX as usize_max;

        assert_eq!(join_size(0, true), Some(0));
        assert_eq!(join_size(0, false), Some(0));

        assert_eq!(join_size(12, true), Some(24));
        assert_eq!(join_size(12, false), Some(23));

        assert_eq!(join_size(usize_max, true), None);
        assert_eq!(join_size(usize_max, false), None);
    }

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
        use ::std::vec::Vec;

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
}
