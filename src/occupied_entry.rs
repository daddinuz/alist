//! Occupied entry view for the entry API.

use core::fmt;

use crate::AList;

/// A view into an occupied entry in an [`AList`](crate::AList).
///
/// This type is produced by [`Entry::Occupied`](crate::Entry::Occupied) and
/// provides direct access to the stored key and value.
pub struct OccupiedEntry<'a, K, V> {
    alist: &'a mut AList<K, V>,
    position: usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub(super) fn new(alist: &'a mut AList<K, V>, position: usize) -> Self {
        Self { alist, position }
    }

    /// Returns a shared reference to the occupied value.
    pub fn get(&self) -> &V {
        let (_, v) = &self.alist.pairs[self.position];
        v
    }

    /// Returns a mutable reference to the occupied value.
    pub fn get_mut(&mut self) -> &mut V {
        let (_, v) = &mut self.alist.pairs[self.position];
        v
    }

    /// Replaces the occupied value and returns the previous value.
    pub fn insert(&mut self, value: V) -> V {
        core::mem::replace(self.get_mut(), value)
    }

    /// Converts this entry into a mutable reference to the occupied value.
    pub fn into_mut(self) -> &'a mut V {
        let (_, v) = &mut self.alist.pairs[self.position];
        v
    }

    /// Returns a shared reference to the occupied key.
    pub fn key(&self) -> &K {
        let (k, _) = &self.alist.pairs[self.position];
        k
    }

    /// Removes the occupied entry and returns its value.
    ///
    /// Remaining entries keep their insertion order.
    pub fn remove(self) -> V {
        let (_, v) = self.alist.pairs.remove(self.position);
        v
    }

    /// Removes the occupied entry and returns its key and value.
    ///
    /// Remaining entries keep their insertion order.
    pub fn remove_entry(self) -> (K, V) {
        self.alist.pairs.remove(self.position)
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

#[cfg(test)]
mod tests {
    use alloc::{format, vec, vec::Vec};

    use crate::{AList, Entry, alist};

    #[test]
    fn get_and_get_mut_access_occupied_value() {
        let mut sut = alist! { 'a' => 1 };

        match sut.entry('a') {
            Entry::Occupied(mut entry) => {
                assert_eq!(entry.get(), &1);
                *entry.get_mut() = 2;
            }
            Entry::Vacant(_) => panic!("expected occupied entry"),
        }

        assert_eq!(sut.get(&'a'), Some(&2));
    }

    #[test]
    fn insert_replaces_value_and_returns_old_value() {
        let mut sut = alist! { 'a' => 1 };

        let old = match sut.entry('a') {
            Entry::Occupied(mut entry) => entry.insert(2),
            Entry::Vacant(_) => panic!("expected occupied entry"),
        };

        assert_eq!(old, 1);
        assert_eq!(sut.get(&'a'), Some(&2));
    }

    #[test]
    fn into_mut_returns_value_reference() {
        let mut sut = alist! { 'a' => 1 };

        match sut.entry('a') {
            Entry::Occupied(entry) => *entry.into_mut() = 2,
            Entry::Vacant(_) => panic!("expected occupied entry"),
        }

        assert_eq!(sut.get(&'a'), Some(&2));
    }

    #[test]
    fn remove_preserves_order_of_remaining_items() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };

        let removed = match sut.entry('b') {
            Entry::Occupied(entry) => entry.remove(),
            Entry::Vacant(_) => panic!("expected occupied entry"),
        };

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(removed, 2);
        assert_eq!(pairs, vec![(&'a', &1), (&'c', &3)]);
    }

    #[test]
    fn remove_entry_preserves_order_of_remaining_items() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };

        let removed = match sut.entry('b') {
            Entry::Occupied(entry) => entry.remove_entry(),
            Entry::Vacant(_) => panic!("expected occupied entry"),
        };

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(removed, ('b', 2));
        assert_eq!(pairs, vec![(&'a', &1), (&'c', &3)]);
    }

    #[test]
    fn debug_formats_key_and_value() {
        let mut sut = AList::new();
        sut.insert('a', 1);

        let output = match sut.entry('a') {
            Entry::Occupied(entry) => format!("{entry:?}"),
            Entry::Vacant(_) => panic!("expected occupied entry"),
        };

        assert_eq!(output, "OccupiedEntry { key: 'a', value: 1 }");
    }
}
