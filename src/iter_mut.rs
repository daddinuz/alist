//! Mutable-value iterator over key-value pairs.

use core::fmt;

type DelegateIterMut<'a, K, V> = core::slice::IterMut<'a, (K, V)>;

/// Iterator over borrowed keys and mutable values in insertion order.
///
/// Keys are yielded by shared reference while values are yielded by mutable
/// reference. This type is returned by [`AList::iter_mut`](crate::AList::iter_mut)
/// and by iterating over `&mut AList`.
pub struct IterMut<'a, K, V> {
    delegate: DelegateIterMut<'a, K, V>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    pub(super) fn from_delegate(delegate: DelegateIterMut<'a, K, V>) -> Self {
        Self { delegate }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next().map(|(k, v)| (&*k, v))
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
        self.delegate.last().map(|(k, v)| (&*k, v))
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n).map(|(k, v)| (&*k, v))
    }
}

impl<'a, K, V> core::iter::FusedIterator for IterMut<'a, K, V> {}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back().map(|(k, v)| (&*k, v))
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n).map(|(k, v)| (&*k, v))
    }
}

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for IterMut<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IterMut")
            .field(&self.delegate.as_slice())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use crate::{AList, alist};

    #[test]
    fn yields_pairs_in_insertion_order_after_removal() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3 };
        assert!(sut.remove(&'b').is_some());

        let mut iter = sut.iter_mut();

        assert_eq!(iter.next(), Some((&'a', &mut 1)));
        assert_eq!(iter.next(), Some((&'c', &mut 3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn supports_exact_size_nth_and_double_ended_iteration() {
        let mut sut = alist! { 'a' => 1, 'b' => 2, 'c' => 3, 'd' => 4 };
        let mut iter = sut.iter_mut();

        assert_eq!(iter.len(), 4);
        assert_eq!(iter.nth(1), Some((&'b', &mut 2)));
        assert_eq!(iter.next_back(), Some((&'d', &mut 4)));
        assert_eq!(iter.nth_back(0), Some((&'c', &mut 3)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn mutates_values_without_changing_keys() {
        let mut sut = alist! { 'a' => 1, 'b' => 2 };

        for (_, value) in sut.iter_mut() {
            *value *= 10;
        }

        assert_eq!(sut.get(&'a'), Some(&10));
        assert_eq!(sut.get(&'b'), Some(&20));
    }

    #[test]
    fn empty_iterator_is_fused() {
        let mut sut: AList<char, i32> = AList::new();
        let mut iter = sut.iter_mut();

        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn debug_shows_remaining_pairs() {
        let mut sut = alist! { 'a' => 1 };

        assert_eq!(format!("{:?}", sut.iter_mut()), "IterMut([('a', 1)])");
    }
}
