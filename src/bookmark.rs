//! Bookmark support for repeated key lookup.
//!
//! A bookmark stores a borrowed key together with the last known position of
//! that key inside an [`AList`](crate::AList). Lookup APIs validate that cached
//! position before using it and refresh the position when removals or
//! insertions make it stale.

use core::borrow::Borrow;
use core::fmt;
use core::marker::PhantomData;

use crate::{AList, FastEq};

/// A cached lookup handle for a key in an [`AList`](crate::AList).
///
/// Bookmarks are useful when the same key is queried repeatedly. When the key
/// is still at the cached position, lookup is constant time. If the list has
/// changed, the lookup falls back to a scan and updates the cached position.
pub struct Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    key: &'q Q,
    pub(super) position: usize,
    phantom: PhantomData<fn() -> AList<K, V>>,
}

impl<'q, Q, K, V> From<&'q Q> for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn from(key: &'q Q) -> Self {
        Self::new(key)
    }
}

impl<'q, Q, K, V> Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    pub(super) const fn new_with_position(key: &'q Q, position: usize) -> Self {
        Self {
            key,
            position,
            phantom: PhantomData,
        }
    }

    /// Creates a bookmark for `key` without a known position.
    ///
    /// This is useful when callers want to construct a bookmark before the key
    /// exists, or when they prefer the first lookup to resolve the position.
    pub const fn new(key: &'q Q) -> Self {
        Self::new_with_position(key, usize::MAX)
    }

    /// Returns the key associated with this bookmark.
    pub fn key(&self) -> &Q {
        self.key
    }
}

impl<'q, Q, K, V> PartialEq for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: FastEq + ?Sized,
{
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl<'q, Q, K, V> fmt::Debug for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: fmt::Debug + FastEq + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bookmark")
            .field("key", &self.key())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use crate::{AList, Bookmark, alist};

    fn assert_send_sync<T: Send + Sync>() {}

    #[test]
    fn bookmark_is_send_and_sync_when_key_is_sync() {
        assert_send_sync::<Bookmark<'static, char, char, i32>>();
    }

    #[test]
    fn bookmark_from_and_new_give_the_same_instances() {
        assert_eq!(Bookmark::from(&'a'), Bookmark::<_, char, i32>::new(&'a'));
    }

    #[test]
    fn bookmark_debug_format() {
        let sut = Bookmark::<_, char, i32>::new(&'a');
        let debug_output = format!("{:?}", sut);

        assert_eq!(debug_output, r#"Bookmark { key: 'a', .. }"#,);
    }

    #[test]
    fn alist_bookmark_records_current_position() {
        let sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };

        let bookmark = sut.bookmark(&'b').unwrap();

        assert_eq!(bookmark.key(), &'b');
        assert_eq!(bookmark.position, 1);
    }

    #[test]
    fn alist_bookmark_returns_none_for_missing_key() {
        let sut: AList<char, i32> = AList::new();

        assert!(sut.bookmark(&'x').is_none());
    }
}
