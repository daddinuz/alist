//! Owning iterator over key-value pairs.

use core::fmt;

type Delegate<K, V> = alloc::vec::IntoIter<(K, V)>;

/// Owning iterator over key-value pairs in insertion order.
///
/// This type is returned by [`AList::into_iter`](crate::AList::into_iter).
pub struct IntoIter<K, V> {
    delegate: Delegate<K, V>,
}

impl<K, V> IntoIter<K, V> {
    pub(super) fn from_delegate(delegate: Delegate<K, V>) -> Self {
        Self { delegate }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next()
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
        self.delegate.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n)
    }
}

impl<K, V> core::iter::FusedIterator for IntoIter<K, V> {}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n)
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

impl<K: Clone, V: Clone> Clone for IntoIter<K, V> {
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

        let pairs: Vec<_> = sut.into_iter().collect();

        assert_eq!(pairs, vec![('a', 1), ('c', 3)]);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut iter = sut.into_iter();

        assert_eq!(iter.len(), 4);
        assert_eq!(iter.nth(1), Some(('b', 2)));
        assert_eq!(iter.next_back(), Some(('d', 4)));
        assert_eq!(iter.nth_back(0), Some(('c', 3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn clone_preserves_iterator_position() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut iter = sut.into_iter();

        assert_eq!(iter.next(), Some(('a', 1)));

        let mut clone = iter.clone();
        assert_eq!(iter.next(), Some(('b', 2)));
        assert_eq!(clone.next(), Some(('b', 2)));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let sut: AList<char, i32> = AList::new();
        let mut iter = sut.into_iter();

        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.into_iter()), "IntoIter([('a', 1)])");
    }
}
