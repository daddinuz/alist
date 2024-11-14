use core::fmt;

use crate::AList;

pub struct OccupiedEntry<'a, K, V> {
    alist: &'a mut AList<K, V>,
    position: usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub(super) fn new(alist: &'a mut AList<K, V>, position: usize) -> Self {
        Self { alist, position }
    }

    pub fn get(&self) -> &V {
        let (_, v) = &self.alist.pairs[self.position];
        v
    }

    pub fn get_mut(&mut self) -> &mut V {
        let (_, v) = &mut self.alist.pairs[self.position];
        v
    }

    pub fn insert(&mut self, value: V) -> V {
        std::mem::replace(self.get_mut(), value)
    }

    pub fn into_mut(self) -> &'a mut V {
        let (_, v) = &mut self.alist.pairs[self.position];
        v
    }

    pub fn key(&self) -> &K {
        let (k, _) = &self.alist.pairs[self.position];
        k
    }

    pub fn remove(self) -> V {
        let (_, v) = self.alist.pairs.swap_remove(self.position);
        v
    }

    pub fn remove_entry(self) -> (K, V) {
        self.alist.pairs.swap_remove(self.position)
    }
}

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for OccupiedEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}
