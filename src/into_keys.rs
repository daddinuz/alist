//! Owning iterator over keys.

use core::fmt;

type Delegate<K, V> = alloc::vec::IntoIter<(K, V)>;

/// Owning iterator over keys in insertion order.
///
/// Values are dropped as iteration advances. This type is returned by
/// [`AList::into_keys`](crate::AList::into_keys).
pub struct IntoKeys<K, V> {
    delegate: Delegate<K, V>,
}

impl<K, V> IntoKeys<K, V> {
    pub(super) fn from_delegate(delegate: Delegate<K, V>) -> Self {
        Self { delegate }
    }
}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next().map(|(k, _)| k)
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
        self.delegate.last().map(|(k, _)| k)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n).map(|(k, _)| k)
    }
}

impl<K, V> core::iter::FusedIterator for IntoKeys<K, V> {}

impl<K, V> ExactSizeIterator for IntoKeys<K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<K, V> DoubleEndedIterator for IntoKeys<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(k, _)| k)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(k, _)| k)
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for IntoKeys<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoKeys")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

impl<K: Clone, V: Clone> Clone for IntoKeys<K, V> {
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
    fn yields_keys_in_insertion_order_after_removal() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3 };
        assert!(sut.remove(&'b').is_some());

        let keys: Vec<_> = sut.into_keys().collect();

        assert_eq!(keys, vec!['a', 'c']);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut keys = sut.into_keys();

        assert_eq!(keys.len(), 4);
        assert_eq!(keys.nth(1), Some('b'));
        assert_eq!(keys.next_back(), Some('d'));
        assert_eq!(keys.nth_back(0), Some('c'));
        assert_eq!(keys.next(), None);
    }

    #[test]
    fn clone_preserves_iterator_position() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut keys = sut.into_keys();

        assert_eq!(keys.next(), Some('a'));

        let mut clone = keys.clone();
        assert_eq!(keys.next(), Some('b'));
        assert_eq!(clone.next(), Some('b'));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let sut: AList<char, i32> = AList::new();
        let mut keys = sut.into_keys();

        assert_eq!(keys.next(), None);
        assert_eq!(keys.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.into_keys()), "IntoKeys([('a', 1)])");
    }
}
