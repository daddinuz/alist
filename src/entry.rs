//! Entry API for in-place insertion and mutation.
//!
//! The entry API mirrors the shape of standard map entry APIs while preserving
//! `AList`'s insertion-order behavior.

use core::fmt;

use crate::{OccupiedEntry, VacantEntry};

/// A view into a single key position in an [`AList`](crate::AList).
pub enum Entry<'a, K, V> {
    /// The key is not present and can be inserted.
    Vacant(VacantEntry<'a, K, V>),
    /// The key is present and its value can be read, modified, or removed.
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Ensures a value is present and returns a mutable reference to it.
    ///
    /// Inserts `default` when this entry is vacant. Existing values are left
    /// unchanged.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Self::Vacant(entry) => entry.insert(default),
            Self::Occupied(entry) => entry.into_mut(),
        }
    }

    /// Ensures a value is present using a lazily evaluated default.
    ///
    /// The closure is called only when this entry is vacant.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Self::Vacant(entry) => entry.insert(default()),
            Self::Occupied(entry) => entry.into_mut(),
        }
    }

    #[inline]
    /// Ensures a value is present using a default derived from the entry key.
    ///
    /// The closure is called only when this entry is vacant.
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Self::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
            Self::Occupied(entry) => entry.into_mut(),
        }
    }

    /// Returns a reference to the entry key.
    pub fn key(&self) -> &K {
        match self {
            Self::Vacant(entry) => entry.key(),
            Self::Occupied(entry) => entry.key(),
        }
    }

    /// Modifies an occupied value in place.
    ///
    /// Vacant entries are left unchanged, allowing fluent entry chains.
    pub fn and_modify<F>(mut self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        if let Self::Occupied(entry) = &mut self {
            f(entry.get_mut());
        }

        self
    }
}

impl<'a, K, V: Default> Entry<'a, K, V> {
    /// Ensures a value is present by inserting [`Default::default`] when vacant.
    pub fn or_default(self) -> &'a mut V {
        match self {
            Self::Vacant(entry) => entry.insert(Default::default()),
            Self::Occupied(entry) => entry.into_mut(),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Vacant(entry) => f.debug_tuple("Entry").field(entry).finish(),
            Self::Occupied(entry) => f.debug_tuple("Entry").field(entry).finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use crate::{AList, Entry};

    #[test]
    fn or_insert_inserts_only_for_vacant_entry() {
        let mut sut = AList::new();

        assert_eq!(sut.entry('a').or_insert(1), &mut 1);
        assert_eq!(sut.entry('a').or_insert(2), &mut 1);
        assert_eq!(sut.get(&'a'), Some(&1));
    }

    #[test]
    fn or_insert_with_is_lazy_for_occupied_entry() {
        let mut sut = AList::new();
        sut.insert('a', 1);
        let mut called = false;

        sut.entry('a').or_insert_with(|| {
            called = true;
            2
        });

        assert!(!called);
        assert_eq!(sut.get(&'a'), Some(&1));
    }

    #[test]
    fn or_insert_with_key_uses_vacant_key() {
        let mut sut = AList::new();

        sut.entry('z').or_insert_with_key(|key| *key as u32);

        assert_eq!(sut.get(&'z'), Some(&122));
    }

    #[test]
    fn and_modify_updates_only_occupied_entry() {
        let mut sut = AList::new();
        sut.insert('a', 1);

        sut.entry('a').and_modify(|value| *value += 1);
        sut.entry('b').and_modify(|value| *value += 1);

        assert_eq!(sut.get(&'a'), Some(&2));
        assert_eq!(sut.get(&'b'), None);
    }

    #[test]
    fn key_returns_entry_key_for_both_variants() {
        let mut sut = AList::new();
        sut.insert('a', 1);

        assert_eq!(sut.entry('a').key(), &'a');
        assert_eq!(sut.entry('b').key(), &'b');
    }

    #[test]
    fn or_default_inserts_default_for_vacant_entry() {
        let mut sut = AList::new();

        sut.entry('a').or_default();

        assert_eq!(sut.get(&'a'), Some(&0));
    }

    #[test]
    fn debug_identifies_occupied_and_vacant_entries() {
        let mut sut = AList::new();
        sut.insert('a', 1);

        let occupied = format!("{:?}", sut.entry('a'));
        let vacant = format!("{:?}", sut.entry('b'));

        assert!(occupied.contains("OccupiedEntry"));
        assert!(vacant.contains("VacantEntry"));
    }

    #[test]
    fn occupied_variant_is_returned_for_existing_key() {
        let mut sut = AList::new();
        sut.insert('a', 1);

        assert!(matches!(sut.entry('a'), Entry::Occupied(_)));
        assert!(matches!(sut.entry('b'), Entry::Vacant(_)));
    }
}
