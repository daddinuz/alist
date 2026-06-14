//! Mutable-reference iterator over values.

use core::fmt;

type Delegate<'a, K, V> = core::slice::IterMut<'a, (K, V)>;

/// Iterator over mutable value references in insertion order.
///
/// This type is returned by [`AList::values_mut`](crate::AList::values_mut).
pub struct ValuesMut<'a, K, V> {
    delegate: Delegate<'a, K, V>,
}

impl<'a, K, V> ValuesMut<'a, K, V> {
    pub(super) fn from_delegate(delegate: Delegate<'a, K, V>) -> Self {
        Self { delegate }
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

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

impl<'a, K, V> core::iter::FusedIterator for ValuesMut<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for ValuesMut<'a, K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for ValuesMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(_, v)| v)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(_, v)| v)
    }
}

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for ValuesMut<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ValuesMut")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use crate::{AList, alist};

    #[test]
    fn yields_values_in_insertion_order_after_removal() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3 };
        assert!(sut.remove(&'b').is_some());

        let mut values = sut.values_mut();

        assert_eq!(values.next(), Some(&mut 1));
        assert_eq!(values.next(), Some(&mut 3));
        assert_eq!(values.next(), None);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut values = sut.values_mut();

        assert_eq!(values.len(), 4);
        assert_eq!(values.nth(1), Some(&mut 2));
        assert_eq!(values.next_back(), Some(&mut 4));
        assert_eq!(values.nth_back(0), Some(&mut 3));
        assert_eq!(values.next(), None);
    }

    #[test]
    fn mutates_values_without_changing_keys() {
        let mut sut = alist! { 'a' => 1, 'b' => 2 };

        for value in sut.values_mut() {
            *value *= 10;
        }

        assert_eq!(sut.get(&'a'), Some(&10));
        assert_eq!(sut.get(&'b'), Some(&20));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let mut sut: AList<char, i32> = AList::new();
        let mut values = sut.values_mut();

        assert_eq!(values.next(), None);
        assert_eq!(values.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let mut sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.values_mut()), "ValuesMut([('a', 1)])");
    }
}
