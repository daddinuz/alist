//! Vacant entry view for the entry API.

use core::fmt;

use crate::AList;

/// A view into a vacant entry in an [`AList`](crate::AList).
///
/// This type is produced by [`Entry::Vacant`](crate::Entry::Vacant) and owns
/// the key that may be inserted.
pub struct VacantEntry<'a, K, V> {
    alist: &'a mut AList<K, V>,
    key: K,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub(super) fn new(alist: &'a mut AList<K, V>, key: K) -> Self {
        Self { alist, key }
    }

    /// Inserts `value` at this vacant entry and returns a mutable reference to it.
    ///
    /// The new key-value pair is appended at the end of the list, preserving
    /// insertion order.
    pub fn insert(self, value: V) -> &'a mut V {
        let pairs = &mut self.alist.pairs;
        let top = pairs.len();
        pairs.push((self.key, value));
        let (_, v) = &mut pairs[top];
        v
    }

    /// Consumes the vacant entry and returns its key without inserting.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Returns a shared reference to the key that would be inserted.
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<'a, K: fmt::Debug, V> fmt::Debug for VacantEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use crate::{AList, Entry};

    #[test]
    fn insert_appends_key_and_returns_inserted_value() {
        let mut sut = AList::new();

        let value = match sut.entry('a') {
            Entry::Vacant(entry) => entry.insert(1),
            Entry::Occupied(_) => panic!("expected vacant entry"),
        };

        assert_eq!(value, &mut 1);
        assert_eq!(sut.get(&'a'), Some(&1));
    }

    #[test]
    fn into_key_returns_uninserted_key() {
        let mut sut: AList<char, i32> = AList::new();

        let key = match sut.entry('a') {
            Entry::Vacant(entry) => entry.into_key(),
            Entry::Occupied(_) => panic!("expected vacant entry"),
        };

        assert_eq!(key, 'a');
        assert!(sut.is_empty());
    }

    #[test]
    fn debug_formats_key_only() {
        let mut sut: AList<char, i32> = AList::new();

        let output = match sut.entry('a') {
            Entry::Vacant(entry) => format!("{entry:?}"),
            Entry::Occupied(_) => panic!("expected vacant entry"),
        };

        assert_eq!(output, "VacantEntry('a')");
    }
}
