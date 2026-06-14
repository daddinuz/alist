//! Argument adapter traits for [`AList`](crate::AList) lookup and removal methods.
//!
//! Most callers do not need to name or implement these traits directly. They
//! exist so methods such as [`AList::get`](crate::AList::get) can accept both
//! borrowed keys and bookmarks without adding separate method names.
//!
//! The crate implements these traits for:
//! - borrowed keys, such as `&K` or `&Q` where `K: Borrow<Q>`,
//! - mutable bookmarks for lookup-style operations,
//! - owned bookmarks for removal operations.

use core::borrow::Borrow;

use crate::{AList, Bookmark, FastEq};

/// Argument accepted by [`AList::get`](crate::AList::get).
///
/// Implemented for borrowed keys and mutable bookmarks.
pub trait Get<K, V> {
    /// Returns a shared reference to the value identified by `self`.
    fn get(self, alist: &AList<K, V>) -> Option<&V>;
}

impl<'q, Q, K, V> Get<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get(self, alist: &AList<K, V>) -> Option<&V> {
        if !alist.is_valid(self) {
            self.position = alist.refresh_position(self.key(), self.position)?;
        }

        let (_, v) = &alist.pairs[self.position];
        Some(v)
    }
}

impl<Q, K, V> Get<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get(self, alist: &AList<K, V>) -> Option<&V> {
        let position = alist.position(self)?;
        let (_, v) = &alist.pairs[position];
        Some(v)
    }
}

/// Argument accepted by [`AList::get_mut`](crate::AList::get_mut).
///
/// Implemented for borrowed keys and mutable bookmarks.
pub trait GetMut<K, V> {
    /// Returns a mutable reference to the value identified by `self`.
    fn get_mut(self, alist: &mut AList<K, V>) -> Option<&mut V>;
}

impl<'q, Q, K, V> GetMut<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get_mut(self, alist: &mut AList<K, V>) -> Option<&mut V> {
        if !alist.is_valid(self) {
            self.position = alist.refresh_position(self.key(), self.position)?;
        }

        let (_, v) = &mut alist.pairs[self.position];
        Some(v)
    }
}

impl<Q, K, V> GetMut<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get_mut(self, alist: &mut AList<K, V>) -> Option<&mut V> {
        let position = alist.position(self)?;
        let (_, v) = &mut alist.pairs[position];
        Some(v)
    }
}

/// Argument accepted by [`AList::get_key_value`](crate::AList::get_key_value).
///
/// Implemented for borrowed keys and mutable bookmarks.
pub trait GetKeyValue<K, V> {
    /// Returns shared references to the stored key and value identified by `self`.
    fn get_key_value(self, alist: &AList<K, V>) -> Option<(&K, &V)>;
}

impl<'q, Q, K, V> GetKeyValue<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get_key_value(self, alist: &AList<K, V>) -> Option<(&K, &V)> {
        if !alist.is_valid(self) {
            self.position = alist.refresh_position(self.key(), self.position)?;
        }

        let (k, v) = &alist.pairs[self.position];
        Some((k, v))
    }
}

impl<Q, K, V> GetKeyValue<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get_key_value(self, alist: &AList<K, V>) -> Option<(&K, &V)> {
        let position = alist.position(self)?;
        let (k, v) = &alist.pairs[position];
        Some((k, v))
    }
}

/// Argument accepted by [`AList::get_key_value_mut`](crate::AList::get_key_value_mut).
///
/// Implemented for borrowed keys and mutable bookmarks.
pub trait GetKeyValueMut<K, V> {
    /// Returns a shared key reference and mutable value reference identified by `self`.
    fn get_key_value_mut(self, alist: &mut AList<K, V>) -> Option<(&K, &mut V)>;
}

impl<'q, Q, K, V> GetKeyValueMut<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get_key_value_mut(self, alist: &mut AList<K, V>) -> Option<(&K, &mut V)> {
        if !alist.is_valid(self) {
            self.position = alist.refresh_position(self.key(), self.position)?;
        }

        let (k, v) = &mut alist.pairs[self.position];
        Some((&*k, v))
    }
}

impl<Q, K, V> GetKeyValueMut<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn get_key_value_mut(self, alist: &mut AList<K, V>) -> Option<(&K, &mut V)> {
        let position = alist.position(self)?;
        let (k, v) = &mut alist.pairs[position];
        Some((&*k, v))
    }
}

/// Argument accepted by [`AList::contains_key`](crate::AList::contains_key).
///
/// Implemented for borrowed keys and mutable bookmarks.
pub trait ContainsKey<K, V> {
    /// Returns whether `self` identifies an existing key in `alist`.
    fn contains_key(self, alist: &AList<K, V>) -> bool;
}

impl<'q, Q, K, V> ContainsKey<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn contains_key(self, alist: &AList<K, V>) -> bool {
        if !alist.is_valid(self) {
            match alist.refresh_position(self.key(), self.position) {
                Some(position) => self.position = position,
                None => return false,
            }
        }

        true
    }
}

impl<Q, K, V> ContainsKey<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn contains_key(self, alist: &AList<K, V>) -> bool {
        alist.position(self).is_some()
    }
}

/// Argument accepted by [`AList::remove`](crate::AList::remove).
///
/// Implemented for borrowed keys and owned bookmarks.
pub trait Remove<K, V> {
    /// Removes the key-value pair identified by `self` and returns the value.
    fn remove(self, alist: &mut AList<K, V>) -> Option<V>;
}

impl<'q, Q, K, V> Remove<K, V> for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn remove(mut self, alist: &mut AList<K, V>) -> Option<V> {
        if !alist.is_valid(&self) {
            self.position = alist.refresh_position(self.key(), self.position)?;
        }

        let (_, v) = alist.pairs.remove(self.position);
        Some(v)
    }
}

impl<Q, K, V> Remove<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn remove(self, alist: &mut AList<K, V>) -> Option<V> {
        alist.position(self).map(|position| {
            let (_, v) = alist.pairs.remove(position);
            v
        })
    }
}

/// Argument accepted by [`AList::remove_entry`](crate::AList::remove_entry).
///
/// Implemented for borrowed keys and owned bookmarks.
pub trait RemoveEntry<K, V> {
    /// Removes the key-value pair identified by `self` and returns it.
    fn remove_entry(self, alist: &mut AList<K, V>) -> Option<(K, V)>;
}

impl<'q, Q, K, V> RemoveEntry<K, V> for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn remove_entry(mut self, alist: &mut AList<K, V>) -> Option<(K, V)> {
        if !alist.is_valid(&self) {
            self.position = alist.refresh_position(self.key(), self.position)?;
        }

        Some(alist.pairs.remove(self.position))
    }
}

impl<Q, K, V> RemoveEntry<K, V> for &Q
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn remove_entry(self, alist: &mut AList<K, V>) -> Option<(K, V)> {
        alist
            .position(self)
            .map(|position| alist.pairs.remove(position))
    }
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};

    use crate::{AList, Bookmark, alist};

    #[test]
    fn get_supports_key_and_bookmark_lookup() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut bookmark = Bookmark::new(&'b');

        assert_eq!(sut.get(&'a'), Some(&1));
        assert_eq!(sut.get(&mut bookmark), Some(&2));
    }

    #[test]
    fn get_returns_none_for_missing_key_and_missing_bookmark() {
        let sut: AList<char, i32> = AList::new();
        let mut bookmark = Bookmark::new(&'x');

        assert_eq!(sut.get(&'x'), None);
        assert_eq!(sut.get(&mut bookmark), None);
    }

    #[test]
    fn get_mut_supports_key_and_bookmark_lookup() {
        let mut sut = alist! { 'a' => 1, 'b' => 2 };
        let mut bookmark = sut.bookmark(&'b').unwrap();

        *sut.get_mut(&'a').unwrap() = 10;
        *sut.get_mut(&mut bookmark).unwrap() = 20;

        assert_eq!(sut.get(&'a'), Some(&10));
        assert_eq!(sut.get(&'b'), Some(&20));
    }

    #[test]
    fn get_key_value_supports_key_and_bookmark_lookup() {
        let sut = alist! { 'a' => 1, 'b' => 2 };
        let mut bookmark = Bookmark::new(&'b');

        assert_eq!(sut.get_key_value(&'a'), Some((&'a', &1)));
        assert_eq!(sut.get_key_value(&mut bookmark), Some((&'b', &2)));
    }

    #[test]
    fn get_key_value_mut_supports_key_and_bookmark_lookup() {
        let mut sut = alist! { 'a' => 1, 'b' => 2 };
        let mut bookmark = Bookmark::new(&'b');

        sut.get_key_value_mut(&'a').unwrap().1.clone_from(&10);
        sut.get_key_value_mut(&mut bookmark)
            .unwrap()
            .1
            .clone_from(&20);

        assert_eq!(sut.get(&'a'), Some(&10));
        assert_eq!(sut.get(&'b'), Some(&20));
    }

    #[test]
    fn contains_key_refreshes_stale_bookmark() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };
        let mut bookmark = sut.bookmark(&'c').unwrap();

        assert_eq!(sut.remove(&'a'), Some(1));

        assert!(sut.contains_key(&mut bookmark));
        assert_eq!(bookmark.position, 1);
    }

    #[test]
    fn remove_by_key_preserves_order() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };

        assert_eq!(sut.remove(&'b'), Some(2));

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'a', &1), (&'c', &3)]);
    }

    #[test]
    fn remove_by_bookmark_refreshes_stale_position() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };
        let bookmark = sut.bookmark(&'c').unwrap();

        assert_eq!(sut.remove(&'a'), Some(1));
        assert_eq!(sut.remove(bookmark), Some(3));

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'b', &2)]);
    }

    #[test]
    fn remove_returns_none_for_missing_key_and_missing_bookmark() {
        let mut sut: AList<char, i32> = AList::new();

        assert_eq!(sut.remove(&'x'), None);
        assert_eq!(sut.remove(Bookmark::new(&'x')), None);
    }

    #[test]
    fn remove_entry_by_key_preserves_order() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };

        assert_eq!(sut.remove_entry(&'b'), Some(('b', 2)));

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'a', &1), (&'c', &3)]);
    }

    #[test]
    fn remove_entry_by_bookmark_refreshes_stale_position() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };
        let bookmark = sut.bookmark(&'c').unwrap();

        assert_eq!(sut.remove_entry(&'a'), Some(('a', 1)));
        assert_eq!(sut.remove_entry(bookmark), Some(('c', 3)));

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'b', &2)]);
    }

    #[test]
    fn bookmark_refresh_finds_reinserted_key_after_previous_position() {
        let mut sut = alist! {
            1 => 'a',
            2 => 'b',
            3 => 'c',
            4 => 'd',
        };
        let mut bookmark = sut.bookmark(&2).unwrap();

        assert_eq!(sut.remove(&2), Some('b'));
        assert_eq!(sut.insert(2, 'B'), None);

        assert_eq!(sut.get(&mut bookmark), Some(&'B'));
    }
}
