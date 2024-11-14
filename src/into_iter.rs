use core::fmt;

type Delegate<K, V> = std::vec::IntoIter<(K, V)>;

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

impl<K, V> std::iter::FusedIterator for IntoIter<K, V> {}

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
