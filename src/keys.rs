//! Shared-reference iterator over keys.

use core::fmt;

type Delegate<'a, K, V> = core::slice::Iter<'a, (K, V)>;

/// Iterator over borrowed keys in insertion order.
///
/// This type is returned by [`AList::keys`](crate::AList::keys).
pub struct Keys<'a, K, V> {
    delegate: Delegate<'a, K, V>,
}

impl<'a, K, V> Keys<'a, K, V> {
    pub(super) fn from_delegate(delegate: Delegate<'a, K, V>) -> Self {
        Self { delegate }
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

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

impl<'a, K, V> core::iter::FusedIterator for Keys<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(k, _)| k)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(k, _)| k)
    }
}

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for Keys<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Keys")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

impl<'a, K, V> Clone for Keys<'a, K, V> {
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

        let keys: Vec<_> = sut.keys().collect();

        assert_eq!(keys, vec![&'a', &'c']);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut keys = sut.keys();

        assert_eq!(keys.len(), 4);
        assert_eq!(keys.nth(1), Some(&'b'));
        assert_eq!(keys.next_back(), Some(&'d'));
        assert_eq!(keys.nth_back(0), Some(&'c'));
        assert_eq!(keys.next(), None);
    }

    #[test]
    fn clone_preserves_iterator_position() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut keys = sut.keys();

        assert_eq!(keys.next(), Some(&'a'));

        let mut clone = keys.clone();
        assert_eq!(keys.next(), Some(&'b'));
        assert_eq!(clone.next(), Some(&'b'));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let sut: AList<char, i32> = AList::new();
        let mut keys = sut.keys();

        assert_eq!(keys.next(), None);
        assert_eq!(keys.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.keys()), "Keys([('a', 1)])");
    }
}
