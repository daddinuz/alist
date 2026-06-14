//! Shared-reference iterator over key-value pairs.

use core::fmt;

type Delegate<'a, K, V> = core::slice::Iter<'a, (K, V)>;

/// Iterator over borrowed key-value pairs in insertion order.
///
/// This type is returned by [`AList::iter`](crate::AList::iter) and by
/// iterating over `&AList`.
pub struct Iter<'a, K, V> {
    delegate: Delegate<'a, K, V>,
}

impl<'a, K, V> Iter<'a, K, V> {
    pub(super) fn from_delegate(delegate: Delegate<'a, K, V>) -> Self {
        Self { delegate }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next().map(|(k, v)| (k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.delegate.size_hint()
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.delegate.count()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.delegate.last().map(|(k, v)| (k, v))
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n).map(|(k, v)| (k, v))
    }
}

impl<'a, K, V> core::iter::FusedIterator for Iter<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(k, v)| (k, v))
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(k, v)| (k, v))
    }
}

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for Iter<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            delegate: self.delegate.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::{format, vec, vec::Vec};

    use crate::{AList, alist};

    #[test]
    fn yields_pairs_in_insertion_order_after_removal() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3 };
        assert!(sut.remove(&'b').is_some());

        let pairs: Vec<_> = sut.iter().collect();

        assert_eq!(pairs, vec![(&'a', &1), (&'c', &3)]);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut iter = sut.iter();

        assert_eq!(iter.len(), 4);
        assert_eq!(iter.nth(1), Some((&'b', &2)));
        assert_eq!(iter.next_back(), Some((&'d', &4)));
        assert_eq!(iter.nth_back(0), Some((&'c', &3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn clone_preserves_iterator_position() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut iter = sut.iter();

        assert_eq!(iter.next(), Some((&'a', &1)));

        let mut clone = iter.clone();
        assert_eq!(iter.next(), Some((&'b', &2)));
        assert_eq!(clone.next(), Some((&'b', &2)));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let sut: AList<char, i32> = AList::new();
        let mut iter = sut.iter();

        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.iter()), "Iter([('a', 1)])");
    }
}
