//! Shared-reference iterator over values.

use core::fmt;

type Delegate<'a, K, V> = core::slice::Iter<'a, (K, V)>;

/// Iterator over borrowed values in insertion order.
///
/// This type is returned by [`AList::values`](crate::AList::values).
pub struct Values<'a, K, V> {
    delegate: Delegate<'a, K, V>,
}

impl<'a, K, V> Values<'a, K, V> {
    pub(super) fn from_delegate(delegate: Delegate<'a, K, V>) -> Self {
        Self { delegate }
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

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

impl<'a, K, V> core::iter::FusedIterator for Values<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(_, v)| v)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(_, v)| v)
    }
}

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for Values<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Values")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

impl<'a, K, V> Clone for Values<'a, K, V> {
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

        let values: Vec<_> = sut.values().collect();

        assert_eq!(values, vec![&1, &3]);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut values = sut.values();

        assert_eq!(values.len(), 4);
        assert_eq!(values.nth(1), Some(&2));
        assert_eq!(values.next_back(), Some(&4));
        assert_eq!(values.nth_back(0), Some(&3));
        assert_eq!(values.next(), None);
    }

    #[test]
    fn clone_preserves_iterator_position() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut values = sut.values();

        assert_eq!(values.next(), Some(&1));

        let mut clone = values.clone();
        assert_eq!(values.next(), Some(&2));
        assert_eq!(clone.next(), Some(&2));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let sut: AList<char, i32> = AList::new();
        let mut values = sut.values();

        assert_eq!(values.next(), None);
        assert_eq!(values.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.values()), "Values([('a', 1)])");
    }
}
