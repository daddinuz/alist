use core::fmt;

use crate::AList;

pub struct VacantEntry<'a, K, V> {
    alist: &'a mut AList<K, V>,
    key: K,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub(super) fn new(alist: &'a mut AList<K, V>, key: K) -> Self {
        Self { alist, key }
    }

    pub fn insert(self, value: V) -> &'a mut V {
        let pairs = &mut self.alist.pairs;
        let top = pairs.len();
        pairs.push((self.key, value));
        let (_, v) = &mut pairs[top];
        v
    }

    pub fn into_key(self) -> K {
        self.key
    }

    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<'a, K: fmt::Debug, V> fmt::Debug for VacantEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}
