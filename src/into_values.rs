//! Owning iterator over values.

use core::fmt;

type Delegate<K, V> = alloc::vec::IntoIter<(K, V)>;

/// Owning iterator over values in insertion order.
///
/// Keys are dropped as iteration advances. This type is returned by
/// [`AList::into_values`](crate::AList::into_values).
pub struct IntoValues<K, V> {
    delegate: Delegate<K, V>,
}

impl<K, V> IntoValues<K, V> {
    pub(super) fn from_delegate(delegate: Delegate<K, V>) -> Self {
        Self { delegate }
    }
}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next().map(|(_, v)| v)
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
        self.delegate.last().map(|(_, v)| v)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n).map(|(_, v)| v)
    }
}

impl<K, V> core::iter::FusedIterator for IntoValues<K, V> {}

impl<K, V> ExactSizeIterator for IntoValues<K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<K, V> DoubleEndedIterator for IntoValues<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(_, v)| v)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(_, v)| v)
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for IntoValues<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoValues")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

impl<K: Clone, V: Clone> Clone for IntoValues<K, V> {
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
    fn yields_values_in_insertion_order_after_removal() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3 };
        assert!(sut.remove(&'b').is_some());

        let values: Vec<_> = sut.into_values().collect();

        assert_eq!(values, vec![1, 3]);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut values = sut.into_values();

        assert_eq!(values.len(), 4);
        assert_eq!(values.nth(1), Some(2));
        assert_eq!(values.next_back(), Some(4));
        assert_eq!(values.nth_back(0), Some(3));
        assert_eq!(values.next(), None);
    }

    #[test]
    fn clone_preserves_iterator_position() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut values = sut.into_values();

        assert_eq!(values.next(), Some(1));

        let mut clone = values.clone();
        assert_eq!(values.next(), Some(2));
        assert_eq!(clone.next(), Some(2));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let sut: AList<char, i32> = AList::new();
        let mut values = sut.into_values();

        assert_eq!(values.next(), None);
        assert_eq!(values.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.into_values()), "IntoValues([('a', 1)])");
    }
}
