use core::fmt;

type Delegate<K, V> = std::vec::IntoIter<(K, V)>;

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

impl<K, V> std::iter::FusedIterator for IntoKeys<K, V> {}

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
