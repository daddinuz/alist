use core::fmt;

use crate::{OccupiedEntry, VacantEntry};

pub enum Entry<'a, K, V> {
    Vacant(VacantEntry<'a, K, V>),
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Self::Vacant(entry) => entry.insert(default),
            Self::Occupied(entry) => entry.into_mut(),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Self::Vacant(entry) => entry.insert(default()),
            Self::Occupied(entry) => entry.into_mut(),
        }
    }

    #[inline]
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Self::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
            Self::Occupied(entry) => entry.into_mut(),
        }
    }

    pub fn key(&self) -> &K {
        match self {
            Self::Vacant(entry) => entry.key(),
            Self::Occupied(entry) => entry.key(),
        }
    }

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
