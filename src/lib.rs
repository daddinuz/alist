#![forbid(unsafe_code)]
#![no_std]

//! # alist
//!
//! `alist` provides an insertion-ordered association list backed by a `Vec`.
//!
//! The crate is `no_std` and uses `alloc` for owned storage.
//!
//! This implementation is backed by a `Vec` of key-value pairs,
//! preserving insertion order across insertions and removals and enabling
//! optimized bookmark lookups in `O(1)` when the bookmarked item has not moved.
//!
//! ## What is an Association List?
//!
//! An **association list (alist)** is a collection of key-value pairs.
//! It provides a lightweight alternative to hash-based and tree-based maps for
//! simple mapping or dictionary-like functionality, especially when the dataset
//! is small and iteration order matters.
//!
//! Like `HashMap`, this implementation does not allow multiple values for the same key:
//! inserting a duplicate key overwrites the existing value while preserving the key's original insertion position.
//!
//! Association lists can avoid hashing and ordering overhead for small
//! datasets, but key-based operations scan linearly and degrade as the dataset grows.
//! Use `AList` only for small inputs and only when keys satisfy [`FastEq`]'s intended contract:
//! compact key types with cheap equality.
//!
//! This crate mitigates repeated lookup costs by leveraging stored positions through the Bookmark API.
//!
//! Items in the `alist` are stored in insertion order. Removing an item shifts later items left while preserving their
//! relative order. Bookmarks account for that by validating and refreshing their stored position.
//!
//! A bookmark is a record of the item's position in the internal vector. If the item is still at that position,
//! access is `O(1)`. If it has moved, a linear search is performed, with a worst-case complexity of `O(n)`, and the
//! bookmark is refreshed.
//!
//! ## Lookup Arguments
//!
//! Lookup methods accept borrowed keys for one-off access. Methods such as [`AList::get`],
//! [`AList::get_mut`], and [`AList::contains_key`] also accept mutable bookmarks so the cached position can be
//! refreshed when needed. Removal methods accept borrowed keys or owned bookmarks; a bookmark is consumed when used for
//! removal because removing the entry invalidates the cached position.
//!
//! These features make `alist` a viable alternative to `HashMap` or `BTreeMap` in scenarios where:
//! - Data removal is infrequent.  
//! - The dataset is small.  
//! - Keys implement [`FastEq`] but do not need to implement `Hash` or `Ord`.  
//!
//! ## Choosing Key and Value Types
//!
//! `AList` stores `(K, V)` pairs contiguously and performs linear scans for key lookup.
//! This makes the size of `K` and `V` important: large keys or values increase the stride between entries and can reduce
//! cache-line efficiency while scanning. Prefer compact keys and values, or store large values behind an indirection such
//! as `Box`, `Rc`, or `Arc`.
//!
//! Key equality also matters. Lookup compares keys repeatedly, so `AList` requires [`FastEq`] to keep lookup APIs focused
//! on key types with cheap equality. `String` does not implement [`FastEq`] because its `Eq` implementation is `O(n)` in
//! the string length. Prefer small identifiers, interned symbols, indices, or other compact keys when possible.
//!
//! ### Key Features:
//! - **Order Preservation**: Items are stored in insertion order across insertions and removals.
//! - **Optimized Retrieval**: Bookmarks support `O(1)` access while their stored positions remain valid.
//! - **Simplicity**: A straightforward design that avoids the overhead of hash-based collections while providing robust functionality.
//!
//! ### Example in Rust:
//! ```rust
//! use alist::AList;
//!
//! let mut alist = AList::new();
//! alist.insert('a', "value1");
//! alist.insert('b', "value2");
//!
//! // Linear lookup
//! if let Some(value) = alist.get(&'a') {
//!     println!("Found: {}", value);
//! }
//!
//! // Fast lookup
//! let mut k2 = alist.bookmark(&'b').unwrap();
//! assert_eq!(alist.get(&mut k2), Some(&"value2"));
//!
//! // Overwriting a value
//! alist.insert('a', "new_value");
//! assert_eq!(alist.get(&'a'), Some(&"new_value"));
//! ```

extern crate alloc;

mod bookmark;
mod entry;
mod fast_eq;
mod into_iter;
mod into_keys;
mod into_values;
mod iter;
mod iter_mut;
mod keys;
mod macros;
mod occupied_entry;
mod sailed;
mod vacant_entry;
mod values;
mod values_mut;

pub use bookmark::Bookmark;
pub use entry::Entry;
pub use fast_eq::FastEq;
pub use into_iter::IntoIter;
pub use into_keys::IntoKeys;
pub use into_values::IntoValues;
pub use iter::Iter;
pub use iter_mut::IterMut;
pub use keys::Keys;
pub use occupied_entry::OccupiedEntry;
pub use vacant_entry::VacantEntry;
pub use values::Values;
pub use values_mut::ValuesMut;

use sailed::{ContainsKey, Get, GetKeyValue, GetKeyValueMut, GetMut, Remove, RemoveEntry};

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::fmt;
use core::hash::{Hash, Hasher};

/// An association list implementation backed by a `Vec` of key-value pairs.
///
/// `AList` preserves insertion order across insertions and removals, making it suitable for scenarios where order matters
/// and removals are infrequent. Lookup and insertion APIs require keys to implement the [`FastEq`] trait.
/// For best performance, choose compact key and value types and keys with trivial equality.
///
/// ## Complexity and Intended Use
///
/// `AList` is a linear collection. Key-based lookup, replacement insertion, removal, and entry access scan the stored
/// pairs and are `O(n)` in the number of entries. Bookmarks can provide `O(1)` access only while their stored position is
/// still valid; otherwise they fall back to a linear scan.
///
/// Use `AList` only for small inputs and only with key types that satisfy [`FastEq`]'s intended contract: compact keys
/// with cheap equality. For larger collections, or keys with expensive equality, prefer a hash-based or tree-based map.
///
/// ### Features
/// - **Order Preservation**: Items are stored in insertion order across insertions and removals.
/// - **Optimized Retrieval**: Bookmarks support `O(1)` access while their stored positions remain valid.
/// - **Simplicity**: A straightforward design that avoids the overhead of hash-based collections while providing robust functionality.
///
/// ### Example
/// ```rust
/// use alist::AList;
///
/// let mut alist = AList::new();
/// alist.insert('a', "value1");
/// alist.insert('b', "value2");
///
/// assert_eq!(alist.get(&'a'), Some(&"value1"));
/// ```
///
/// Use `AList` for small datasets, infrequent removals, or keys that implement `FastEq` but do not need `Hash` or `Ord`.
pub struct AList<K, V> {
    pairs: Vec<(K, V)>,
}

impl<K: FastEq, V> FromIterator<(K, V)> for AList<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut this = Self::new();
        this.extend(iter);
        this
    }
}

impl<K, V> Default for AList<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> AList<K, V> {
    /// Creates a new, empty `AList`.
    ///
    /// This method initializes an empty association list, ready to store key-value pairs.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let alist: AList<char, &str> = AList::new();
    /// assert!(alist.is_empty());
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self { pairs: Vec::new() }
    }

    /// Creates a new `AList` with a specified initial capacity.
    ///
    /// This method pre-allocates space for the specified number of key-value pairs,
    /// reducing the need for reallocations as the list grows.
    ///
    /// ### Parameters
    /// - `capacity`: The number of key-value pairs to allocate space for initially.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let alist: AList<char, &str> = AList::with_capacity(10);
    /// assert!(alist.is_empty());
    /// assert!(alist.capacity() >= 10, "Expected the capacity to be at least 10");
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            pairs: Vec::with_capacity(capacity),
        }
    }

    /// Creates a bookmark for the specified key.
    ///
    /// This method allows you to "bookmark" a key in the association list, which can be used for more efficient
    /// retrieval of the corresponding value later. The bookmark stores the position of the key in the internal vector,
    /// and if the key is still at that position, retrieving it by this bookmark will be `O(1)`. Otherwise, a linear
    /// search is performed and the bookmark is updated.
    ///
    /// ### Parameters
    /// - `key`: A reference to the key to bookmark. The key must implement `Borrow<Q>`, and `Q` must implement `FastEq`.
    ///
    /// ### Returns
    /// - `Some(Bookmark)` if the key exists in the list, otherwise `None`.
    ///
    /// ### Example
    /// ```rust
    /// use alist::{AList, Bookmark};
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    /// alist.insert('b', "value2");
    ///
    /// if let Some(mut bookmark) = alist.bookmark(&'a') {
    ///     assert_eq!(alist.get(&mut bookmark), Some(&"value1"));
    /// }
    /// ```
    #[must_use]
    pub fn bookmark<'q, Q>(&self, key: &'q Q) -> Option<Bookmark<'q, Q, K, V>>
    where
        K: Borrow<Q>,
        Q: FastEq + ?Sized,
    {
        let position = self.position(key)?;
        Some(Bookmark::new_with_position(key, position))
    }

    /// Returns an entry for the specified key in the `AList`, allowing for insertion or modification.
    ///
    /// This method provides an `Entry` API, enabling you to insert a value if the key is not already present
    /// or modify the value if the key exists. The `Entry` API is useful for operations that depend on whether
    /// the key is already in the list.
    ///
    /// ### Parameters
    /// - `key`: The key to look up or insert in the `AList`. The key must implement `FastEq`.
    ///
    /// ### Returns
    /// - An `Entry` object, which can be used to insert or modify a value associated with the key.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    ///
    /// // Insert a value if the key doesn't exist
    /// alist.entry('a').or_insert("value1");
    ///
    /// // Modify the value if the key exists
    /// alist.entry('a').and_modify(|v| *v = "new_value");
    ///
    /// assert_eq!(alist.get(&'a'), Some(&"new_value"));
    /// ```
    #[must_use]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    where
        K: FastEq,
    {
        if let Some(position) = self.position(&key) {
            return Entry::Occupied(OccupiedEntry::new(self, position));
        }

        Entry::Vacant(VacantEntry::new(self, key))
    }

    /// Inserts a key-value pair into the `AList`.
    ///
    /// If the key already exists in the `AList`, its value is updated to the provided `value`, and the old value is returned.
    /// The existing key keeps its insertion position. If the key does not exist, the new pair is appended to the list.
    /// Time complexity is O(n).
    ///
    /// ### Parameters
    /// - `key`: The key to insert or update. Must implement `FastEq`.
    /// - `value`: The value to associate with the key.
    ///
    /// ### Returns
    /// - `Some(V)` containing the previous value associated with the key if it already existed.
    /// - `None` if the key was not present in the `AList`.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    ///
    /// // Insert a new key-value pair
    /// assert!(alist.insert('a', "value1").is_none());
    ///
    /// // Update an existing key
    /// assert_eq!(alist.insert('a', "new_value"), Some("value1"));
    ///
    /// // Check the updated value
    /// assert_eq!(alist.get(&'a'), Some(&"new_value"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: FastEq,
    {
        if let Some(position) = self.position(&key) {
            let (_, v) = &mut self.pairs[position];
            return Some(core::mem::replace(v, value));
        }

        self.pairs.push((key, value));
        None
    }

    /// Retrieves a reference to the value associated with the given key in the `AList`.
    ///
    /// The lookup argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or a mutable [`Bookmark`]. Bookmark lookups refresh the cached position when it is stale.
    /// If the key exists in the `AList`, a reference to the associated value is returned.
    /// Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or mutable bookmark used to locate the value.
    ///
    /// ### Returns
    /// - `Some(&V)` if the key exists in the `AList`.
    /// - `None` if the key is not found.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    ///
    /// // Retrieve a value by key
    /// assert_eq!(alist.get(&'a'), Some(&"value1"));
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get(&'b').is_none());
    ///
    /// // Retrieve a value by its bookmark
    /// let mut k1 = alist.bookmark(&'a').unwrap();
    /// assert_eq!(alist.get(&mut k1), Some(&"value1"));
    /// ```
    #[must_use]
    pub fn get(&self, key: impl Get<K, V>) -> Option<&V> {
        key.get(self)
    }

    /// Retrieves a mutable reference to the value associated with the given key in the `AList`.
    ///
    /// The lookup argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or a mutable [`Bookmark`]. Bookmark lookups refresh the cached position when it is stale.
    /// If the key exists in the `AList`, a mutable reference to the associated value is returned.
    /// Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or mutable bookmark used to locate the value.
    ///
    /// ### Returns
    /// - `Some(&mut V)` if the key exists in the `AList`.
    /// - `None` if the key is not found.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    ///
    /// // Retrieve a value by key
    /// assert_eq!(alist.get_mut(&'a'), Some(&mut "value1"));
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get_mut(&'b').is_none());
    ///
    /// // Retrieve a value by its bookmark
    /// let mut k1 = alist.bookmark(&'a').unwrap();
    /// assert_eq!(alist.get_mut(&mut k1), Some(&mut "value1"));
    /// ```
    #[must_use]
    pub fn get_mut(&mut self, key: impl GetMut<K, V>) -> Option<&mut V> {
        key.get_mut(self)
    }

    /// Retrieves a reference to the key and its associated value in the `AList`.
    ///
    /// The lookup argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or a mutable [`Bookmark`]. Bookmark lookups refresh the cached position when it is stale.
    /// If the key exists in the `AList`, a reference to the stored key and its associated value is returned as a tuple.
    /// Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or mutable bookmark used to locate the key-value pair.
    ///
    /// ### Returns
    /// - `Some((&K, &V))` if the key exists in the `AList`, containing references to the key and value.
    /// - `None` if the key is not found.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    ///
    /// // Retrieve a key-value pair by key
    /// if let Some((k, v)) = alist.get_key_value(&'a') {
    ///     assert_eq!(k, &'a');
    ///     assert_eq!(v, &"value1");
    /// }
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get_key_value(&'b').is_none());
    ///
    /// // Retrieve a value by its bookmark
    /// let mut k1 = alist.bookmark(&'a').unwrap();
    /// assert_eq!(alist.get_key_value(&mut k1), Some((&'a', &"value1")));
    /// ```
    #[must_use]
    pub fn get_key_value(&self, key: impl GetKeyValue<K, V>) -> Option<(&K, &V)> {
        key.get_key_value(self)
    }

    /// Retrieves a mutable reference to the key and its associated value in the `AList`.
    ///
    /// The lookup argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or a mutable [`Bookmark`]. Bookmark lookups refresh the cached position when it is stale.
    /// If the key exists in the `AList`, a reference to the stored key and its associated mutable value is returned as a tuple.
    /// Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or mutable bookmark used to locate the key-value pair.
    ///
    /// ### Returns
    /// - `Some((&K, &mut V))` if the key exists in the `AList`, containing references to the key and value.
    /// - `None` if the key is not found.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    ///
    /// // Retrieve a key-value pair by key
    /// if let Some((k, v)) = alist.get_key_value_mut(&'a') {
    ///     assert_eq!(k, &'a');
    ///     assert_eq!(v, &mut "value1");
    /// }
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get_key_value_mut(&'b').is_none());
    ///
    /// // Retrieve a value by its bookmark
    /// let mut k1 = alist.bookmark(&'a').unwrap();
    /// assert_eq!(alist.get_key_value_mut(&mut k1), Some((&'a', &mut "value1")));
    /// ```
    #[must_use]
    pub fn get_key_value_mut(&mut self, key: impl GetKeyValueMut<K, V>) -> Option<(&K, &mut V)> {
        key.get_key_value_mut(self)
    }

    /// Checks if the given key exists in the `AList`.
    ///
    /// The lookup argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or a mutable [`Bookmark`]. Bookmark checks refresh the cached position when it is stale.
    /// It returns `true` if the key is present in the `AList`, and `false` otherwise.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or mutable bookmark used to determine if the key exists.
    ///
    /// ### Returns
    /// - `true` if the key exists in the `AList`.
    /// - `false` if the key is not found.
    ///
    /// ### Example
    /// ```rust
    /// use alist::{AList, Bookmark};
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    ///
    /// // Check for the existence of a key
    /// assert!(alist.contains_key(&'a'));
    /// assert!(!alist.contains_key(&'b'));
    ///
    /// // Check for the existence of a key by its bookmark
    /// let mut k1 = alist.bookmark(&'a').unwrap();
    /// assert!(alist.contains_key(&mut k1));
    /// let mut k2 = Bookmark::new(&'b');
    /// assert!(!alist.contains_key(&mut k2));
    /// ```
    #[must_use]
    pub fn contains_key(&self, key: impl ContainsKey<K, V>) -> bool {
        key.contains_key(self)
    }

    /// Removes a key-value pair from the `AList`.
    ///
    /// The removal argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or an owned [`Bookmark`]. Removing by bookmark consumes it because removal invalidates the cached position.
    /// If the key exists in the `AList`, the pair is removed, and the associated value is returned.
    /// Remaining pairs keep their insertion order.
    /// If the key does not exist, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or owned bookmark used to locate the key-value pair to remove.
    ///
    /// ### Returns
    /// - `Some(V)` containing the value associated with the removed key if it existed.
    /// - `None` if the key was not found in the `AList`.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    /// alist.insert('b', "value2");
    ///
    /// // Remove an existing key
    /// assert_eq!(alist.remove(&'a'), Some("value1"));
    /// assert!(!alist.contains_key(&'a'));
    ///
    /// // Remove an existing key by its bookmark
    /// let k2 = alist.bookmark(&'b').unwrap();
    /// assert_eq!(alist.remove(k2), Some("value2"));
    /// assert!(!alist.contains_key(&'b'));
    ///
    /// // Attempt to remove a non-existent key
    /// assert!(alist.remove(&'b').is_none());
    /// ```
    #[must_use]
    pub fn remove(&mut self, key: impl Remove<K, V>) -> Option<V> {
        key.remove(self)
    }

    /// Removes a key-value pair from the `AList` and returns it as a tuple.
    ///
    /// The removal argument can be a borrowed key, such as `&K` or `&Q` where `K: Borrow<Q>`,
    /// or an owned [`Bookmark`]. Removing by bookmark consumes it because removal invalidates the cached position.
    /// If the key exists in the `AList`, the pair is removed, and the key and value are returned as a tuple.
    /// Remaining pairs keep their insertion order.
    /// If the key does not exist, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: A borrowed key or owned bookmark used to locate the key-value pair to remove.
    ///
    /// ### Returns
    /// - `Some((K, V))` containing the removed key and its associated value if the key existed.
    /// - `None` if the key was not found in the `AList`.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', "value1");
    /// alist.insert('b', "value2");
    ///
    /// // Remove an existing key-value pair
    /// assert_eq!(alist.remove_entry(&'a'), Some(('a', "value1")));
    /// assert!(!alist.contains_key(&'a'));
    ///
    /// // Remove an existing key-value pair by its bookmark
    /// let k2 = alist.bookmark(&'b').unwrap();
    /// assert_eq!(alist.remove_entry(k2), Some(('b', "value2")));
    /// assert!(!alist.contains_key(&'b'));
    ///
    /// // Attempt to remove a non-existent key
    /// assert!(alist.remove_entry(&'z').is_none());
    /// ```
    #[must_use]
    pub fn remove_entry(&mut self, key: impl RemoveEntry<K, V>) -> Option<(K, V)> {
        key.remove_entry(self)
    }

    /// Retains only the key-value pairs in the `AList` that satisfy a predicate.
    ///
    /// This method takes a closure and applies it to each key-value pair in the `AList`.
    /// Only pairs for which the closure returns `true` are kept in the list; others are removed.
    ///
    /// ### Parameters
    /// - `f`: A closure of the form `FnMut(&K, &V) -> bool`, applied to each key-value pair.
    ///   If the closure returns `true`, the pair is retained; otherwise, it is removed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    /// alist.insert('c', 3);
    ///
    /// // Retain only pairs where the value is greater than 1
    /// alist.retain(|_, v| *v > 1);
    ///
    /// assert!(!alist.contains_key(&'a'));
    /// assert!(alist.contains_key(&'b'));
    /// assert!(alist.contains_key(&'c'));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &V) -> bool,
    {
        self.pairs.retain(|(k, v)| f(k, v));
    }

    /// Retains only the key-value pairs in the `AList` that satisfy a predicate, allowing mutable access to the values.
    ///
    /// This method takes a closure that provides mutable access to the values during the retention process.
    /// Key-value pairs for which the closure returns `true` are kept in the list, while others are removed.
    ///
    /// ### Parameters
    /// - `f`: A closure of the form `FnMut(&K, &mut V) -> bool`, applied to each key-value pair.
    ///   If the closure returns `true`, the pair is retained; otherwise, it is removed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    /// alist.insert('c', 3);
    ///
    /// // Retain pairs where the value is odd, and double the values
    /// alist.retain_mut(|_, v| {
    ///     if (*v & 1) != 0 {
    ///         *v *= 2;
    ///         true
    ///     } else {
    ///         false
    ///     }
    /// });
    ///
    /// assert_eq!(alist.get(&'a'), Some(&2));
    /// assert!(!alist.contains_key(&'b'));
    /// assert_eq!(alist.get(&'c'), Some(&6));
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.pairs.retain_mut(|(k, v)| f(k, v));
    }

    #[inline]
    #[must_use]
    fn position<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: FastEq + ?Sized,
    {
        // Centralized key lookup strategy: if duplicate pairs ever exist
        // internally, key-based operations target the last matching pair.
        self.pairs.iter().rposition(|(k, _)| k.borrow() == key)
    }

    #[must_use]
    fn refresh_position<Q>(&self, key: &Q, previous_position: usize) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: FastEq + ?Sized,
    {
        let len = self.pairs.len();
        if len == 0 {
            return None;
        }

        let start = previous_position.min(len - 1);

        // Public APIs keep keys unique, so search order does not change the
        // result. Prefer the area at or before the previous position because
        // order-preserving removals shift stale bookmarks left.
        if let Some(position) = self.pairs[..=start]
            .iter()
            .rposition(|(k, _)| k.borrow() == key)
        {
            return Some(position);
        }

        self.pairs[start + 1..]
            .iter()
            .rposition(|(k, _)| k.borrow() == key)
            .map(|position| start + 1 + position)
    }

    #[must_use]
    fn is_valid<Q>(&self, bookmark: &Bookmark<Q, K, V>) -> bool
    where
        K: Borrow<Q>,
        Q: FastEq + ?Sized,
    {
        self.pairs
            .get(bookmark.position)
            .map(|(k, _)| k.borrow() == bookmark.key())
            .unwrap_or(false)
    }
}

impl<K: FastEq, V> Extend<(K, V)> for AList<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let pairs = iter.into_iter();

        let (lower, _) = pairs.size_hint();
        self.reserve(lower);

        for (key, value) in pairs {
            if let Some(position) = self.position(&key) {
                let (_, v) = &mut self.pairs[position];
                *v = value;
            } else {
                self.pairs.push((key, value));
            }
        }
    }
}

impl<'a, K: FastEq + Clone, V: Clone> Extend<(&'a K, &'a V)> for AList<K, V> {
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, values: T) {
        self.extend(values.into_iter().map(|(k, v)| (k.clone(), v.clone())))
    }
}

impl<K, V> AList<K, V> {
    /// Reduces the capacity of the `AList` as much as possible.
    ///
    /// This method ensures that the capacity of the underlying storage is equal to or just larger than the
    /// current length of the `AList`. It can help reduce memory usage when the list has grown beyond its needs.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::with_capacity(100);
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// assert!(alist.capacity() >= 100);
    /// alist.shrink_to_fit();
    /// assert!(alist.capacity() >= alist.len());
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.pairs.shrink_to_fit();
    }

    /// Shrinks the capacity of the `AList` to the specified minimum, if possible.
    ///
    /// If the current capacity is greater than the specified minimum and the minimum is at least as large as
    /// the current length of the `AList`, this method reduces the capacity. Otherwise, the capacity remains unchanged.
    ///
    /// ### Parameters
    /// - `min_capacity`: The minimum capacity to shrink the `AList` to. Must be at least the current length.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::with_capacity(100);
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// assert!(alist.capacity() >= 100);
    /// alist.shrink_to(10);
    /// assert!(alist.capacity() >= 10);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.pairs.shrink_to(min_capacity);
    }

    /// Reserves capacity for at least the specified number of elements.
    ///
    /// This method ensures that the `AList` can hold at least the specified number of elements without reallocating.
    /// If the current capacity is already sufficient, no change is made; otherwise, the capacity is increased.
    ///
    /// ### Parameters
    /// - `additional`: The minimum number of elements to reserve space for. The `AList` will have enough capacity to
    ///   accommodate these elements without reallocating.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist: AList<char, i32> = AList::new();
    /// alist.reserve(100);
    /// assert!(alist.capacity() >= 100);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.pairs.reserve(additional);
    }

    /// Reserves exactly the specified number of elements' worth of capacity.
    ///
    /// This method ensures that the `AList` has enough capacity for at least the specified number of elements.
    /// Unlike `reserve`, it may allocate exactly the amount needed to hold that many elements, without
    /// over-allocating space.
    ///
    /// ### Parameters
    /// - `additional`: The exact number of elements to reserve space for. The `AList` will have enough capacity to
    ///   accommodate these elements, with no extra space.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist: AList<char, i32> = AList::new();
    /// alist.reserve_exact(100);
    /// assert!(alist.capacity() >= 100);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.pairs.reserve_exact(additional);
    }

    /// Returns the number of elements the `AList` can hold without reallocating.
    ///
    /// This method returns the current capacity of the `AList`, which represents the number of elements the list can
    /// store without needing to allocate additional space. The capacity is not necessarily equal to the number of elements
    /// in the list (which is returned by the `len` method), as it may include extra reserved space.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// assert!(alist.capacity() >= 0); // The initial capacity might not be zero.
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    /// assert!(alist.capacity() >= 2); // Capacity is greater than or equal to the number of inserted elements.
    /// ```
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.pairs.capacity()
    }

    /// Returns the number of elements in the `AList`.
    ///
    /// This method returns the number of key-value pairs currently stored in the `AList`. It does not include any
    /// unused capacity or space reserved, only the actual elements in the list.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    /// assert_eq!(alist.len(), 2);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.pairs.len()
    }

    /// Returns `true` if the `AList` contains no elements, otherwise `false`.
    ///
    /// This method checks whether the `AList` has any key-value pairs. It returns `true` if there are no elements,
    /// and `false` otherwise.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// assert!(alist.is_empty());
    /// alist.insert('a', 1);
    /// assert!(!alist.is_empty());
    /// alist.clear();
    /// assert!(alist.is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }

    /// Removes all elements from the `AList`.
    ///
    /// This method clears the list, removing all key-value pairs. The capacity of the `AList` is not affected,
    /// so the next time the list grows, it will start from the same allocated capacity.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    /// assert_eq!(alist.len(), 2);
    ///
    /// alist.clear();
    /// assert_eq!(alist.len(), 0);
    /// assert!(alist.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.pairs.clear();
    }

    /// Returns an iterator over the keys of the `AList`.
    ///
    /// This method returns an iterator that yields references to the keys of the key-value pairs stored in the `AList`.
    /// The keys are yielded in insertion order.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// let keys: Vec<_> = alist.keys().collect();
    /// assert_eq!(&keys[..], &[&'a', &'b']);
    /// ```
    #[must_use]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::from_delegate(self.pairs.iter())
    }

    /// Consumes the `AList` and returns an iterator over the keys.
    ///
    /// This method consumes the `AList` and returns an iterator that yields keys in insertion order.
    /// After calling `into_keys`, the `AList` is no longer accessible as it has been consumed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// let keys: Vec<_> = alist.into_keys().collect();
    /// assert_eq!(keys, vec!['a', 'b']);
    /// ```
    #[must_use]
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys::from_delegate(self.pairs.into_iter())
    }

    /// Returns an iterator over the values of the `AList`.
    ///
    /// This method returns an iterator that yields references to the values of the key-value pairs stored in the `AList`.
    /// The values are yielded in insertion order.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// let values: Vec<_> = alist.values().collect();
    /// assert_eq!(values, vec![&1, &2]);
    /// ```
    #[must_use]
    pub fn values(&self) -> Values<'_, K, V> {
        Values::from_delegate(self.pairs.iter())
    }

    /// Returns a mutable iterator over the values of the `AList`.
    ///
    /// This method returns a mutable iterator that allows modifying the values of the key-value pairs stored in the `AList`.
    /// The values are yielded in insertion order.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// for value in alist.values_mut() {
    ///     *value *= 2;  // Doubling each value
    /// }
    ///
    /// let values: Vec<_> = alist.values().collect();
    /// assert_eq!(&values[..], &[&2, &4]);
    /// ```
    #[must_use]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut::from_delegate(self.pairs.iter_mut())
    }

    /// Consumes the `AList` and returns an iterator over the values.
    ///
    /// This method consumes the `AList` and returns an iterator that yields values in insertion order.
    /// After calling `into_values`, the `AList` is no longer accessible as it has been consumed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// let values: Vec<_> = alist.into_values().collect();
    /// assert_eq!(values, vec![1, 2]);
    /// ```
    #[must_use]
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues::from_delegate(self.pairs.into_iter())
    }

    /// Returns an iterator over the key-value pairs of the `AList`.
    ///
    /// This method returns an iterator that yields references to key-value pairs in insertion order.
    /// The iterator allows read-only access to both the keys and values.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// let pairs: Vec<_> = alist.iter().collect();
    /// assert_eq!(&pairs[..], &[(&'a', &1), (&'b', &2)]);
    /// ```
    #[must_use]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::from_delegate(self.pairs.iter())
    }

    /// Returns a mutable iterator over the key-value pairs of the `AList`.
    ///
    /// This method returns a mutable iterator that allows reading keys and modifying values of the key-value pairs stored
    /// in the `AList`. The iterator yields pairs in insertion order.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert('a', 1);
    /// alist.insert('b', 2);
    ///
    /// for (_key, value) in alist.iter_mut() {
    ///     *value *= 2;  // Doubling each value
    /// }
    ///
    /// let values: Vec<_> = alist.values().collect();
    /// assert_eq!(&values[..], &[&2, &4]);
    /// ```
    #[must_use]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::from_delegate(self.pairs.iter_mut())
    }
}

impl<K, V> IntoIterator for AList<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from_delegate(self.pairs.into_iter())
    }
}

impl<'a, K, V> IntoIterator for &'a AList<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut AList<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K: Clone, V: Clone> Clone for AList<K, V> {
    fn clone(&self) -> Self {
        Self {
            pairs: self.pairs.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.pairs.clone_from(&source.pairs)
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for AList<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        self.pairs.iter().for_each(|(k, v)| {
            map.entry(k, v);
        });
        map.finish()
    }
}

impl<K: FastEq, V: PartialEq> PartialEq for AList<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().all(|(k, v)| other.get(k) == Some(v))
    }
}

impl<K: FastEq, V: Eq> Eq for AList<K, V> {}

impl<K: Hash, V: Hash> Hash for AList<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut sum = 0_u64;
        let mut xor = 0_u64;

        for pair in &self.pairs {
            let hash = hash_one(pair);
            sum = sum.wrapping_add(hash);
            xor ^= hash.rotate_left(32);
        }

        state.write_usize(self.len());
        state.write_u64(sum);
        state.write_u64(xor);
    }
}

fn hash_one<T: Hash + ?Sized>(value: &T) -> u64 {
    let mut hasher = AListHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

struct AListHasher(u64);

impl Default for AListHasher {
    fn default() -> Self {
        // 64-bit FNV-1a offset basis. This private hasher is only used to
        // produce deterministic per-pair hashes before order-independent
        // aggregation; the final hash is still written into the caller's hasher.
        Self(0xcbf2_9ce4_8422_2325)
    }
}

impl Hasher for AListHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            // 64-bit FNV prime.
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::{format, vec, vec::Vec};

    use crate::{AList, alist};

    #[test]
    fn hash_is_order_independent_for_equal_lists() {
        let l = alist! {
            'x' => 1,
            'y' => 2,
            'z' => 3,
        };
        let r = alist! {
            'z' => 3,
            'y' => 2,
            'x' => 1,
        };

        assert_eq!(l, r);
        assert_eq!(super::hash_one(&l), super::hash_one(&r));
    }

    #[test]
    fn hash_includes_keys() {
        let l = alist! { 'a' => 1 };
        let r = alist! { 'b' => 1 };

        assert_ne!(super::hash_one(&l), super::hash_one(&r));
    }

    #[test]
    fn constructors_create_empty_lists_with_expected_capacity() {
        let new: AList<char, i32> = AList::new();
        let default: AList<char, i32> = AList::default();
        let with_capacity: AList<char, i32> = AList::with_capacity(8);

        assert!(new.is_empty());
        assert!(default.is_empty());
        assert!(with_capacity.is_empty());
        assert!(with_capacity.capacity() >= 8);
    }

    #[test]
    fn insert_adds_new_keys_and_replaces_existing_values() {
        let mut sut = AList::new();

        assert_eq!(sut.insert('a', 1), None);
        assert_eq!(sut.insert('b', 2), None);
        assert_eq!(sut.insert('a', 3), Some(1));

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'a', &3), (&'b', &2)]);
    }

    #[test]
    fn from_iter_and_extend_keep_first_key_position_for_duplicates() {
        let mut sut = [('a', 1), ('b', 2), ('a', 3)]
            .into_iter()
            .collect::<AList<_, _>>();

        sut.extend([('c', 4), ('b', 5)]);

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'a', &3), (&'b', &5), (&'c', &4)]);
    }

    #[test]
    fn key_based_operations_target_last_matching_internal_pair() {
        let mut sut = AList {
            pairs: vec![('a', 1), ('b', 2), ('a', 3)],
        };

        assert_eq!(sut.position(&'a'), Some(2));
        assert_eq!(sut.get(&'a'), Some(&3));
        assert_eq!(sut.get_key_value(&'a'), Some((&'a', &3)));
        assert_eq!(sut.insert('a', 4), Some(3));

        assert_eq!(sut.get_mut(&'a').map(|value| *value), Some(4));
        *sut.get_key_value_mut(&'a').unwrap().1 = 5;
        sut.extend([('a', 6)]);
        assert_eq!(sut.remove(&'a'), Some(6));

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'a', &1), (&'b', &2)]);
    }

    #[test]
    fn refresh_position_searches_before_previous_position_then_after_it() {
        let sut = AList {
            pairs: vec![('a', 1), ('b', 2), ('c', 3), ('d', 4)],
        };

        assert_eq!(sut.refresh_position(&'b', 3), Some(1));
        assert_eq!(sut.refresh_position(&'d', 0), Some(3));
        assert_eq!(sut.refresh_position(&'c', usize::MAX), Some(2));
        assert_eq!(sut.refresh_position(&'x', 2), None);
    }

    #[test]
    fn extend_from_references_clones_keys_and_values() {
        let source = [('a', 1), ('b', 2)];
        let mut sut = AList::new();

        sut.extend(source.iter().map(|(key, value)| (key, value)));

        assert_eq!(sut.get(&'a'), Some(&1));
        assert_eq!(sut.get(&'b'), Some(&2));
    }

    #[test]
    fn retain_filters_pairs_without_reordering_survivors() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
            'd' => 4,
        };

        sut.retain(|_, value| value % 2 == 0);

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'b', &2), (&'d', &4)]);
    }

    #[test]
    fn retain_mut_can_modify_surviving_values() {
        let mut sut = alist! {
            'a' => 1,
            'b' => 2,
            'c' => 3,
        };

        sut.retain_mut(|_, value| {
            if *value % 2 == 1 {
                *value *= 10;
                true
            } else {
                false
            }
        });

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(pairs, vec![(&'a', &10), (&'c', &30)]);
    }

    #[test]
    fn reserve_and_shrink_manage_capacity_without_changing_items() {
        let mut sut = alist! { 'a' => 1, 'b' => 2 };

        sut.reserve(16);
        assert!(sut.capacity() >= 18);

        sut.shrink_to(4);
        assert!(sut.capacity() >= 4);
        assert_eq!(sut.len(), 2);
        assert_eq!(sut.get(&'a'), Some(&1));
        assert_eq!(sut.get(&'b'), Some(&2));

        sut.shrink_to_fit();
        assert!(sut.capacity() >= sut.len());
    }

    #[test]
    fn reserve_exact_handles_zero_and_existing_capacity() {
        let mut sut: AList<char, i32> = AList::with_capacity(4);
        let capacity = sut.capacity();

        sut.reserve_exact(0);
        sut.reserve_exact(2);

        assert_eq!(sut.capacity(), capacity);
    }

    #[test]
    fn clear_removes_items_but_keeps_capacity_available() {
        let mut sut = AList::with_capacity(8);
        sut.insert('a', 1);
        sut.insert('b', 2);
        let capacity = sut.capacity();

        sut.clear();

        assert!(sut.is_empty());
        assert_eq!(sut.len(), 0);
        assert!(sut.capacity() >= capacity);
    }

    #[test]
    fn clone_is_independent_from_source_after_clone() {
        let mut sut = alist! { 'a' => 1, 'b' => 2 };
        let clone = sut.clone();

        sut.insert('c', 3);

        assert_eq!(clone.get(&'a'), Some(&1));
        assert_eq!(clone.get(&'b'), Some(&2));
        assert_eq!(clone.get(&'c'), None);
    }

    #[test]
    fn equality_is_order_independent_but_checks_keys_values_and_length() {
        let l = alist! { 'a' => 1, 'b' => 2 };
        let same_different_order = alist! { 'b' => 2, 'a' => 1 };
        let different_value = alist! { 'a' => 1, 'b' => 3 };
        let different_key = alist! { 'a' => 1, 'c' => 2 };
        let different_len = alist! { 'a' => 1 };

        assert_eq!(l, same_different_order);
        assert_ne!(l, different_value);
        assert_ne!(l, different_key);
        assert_ne!(l, different_len);
    }

    #[test]
    fn debug_uses_current_insertion_order() {
        let mut sut = alist! {
            'b' => 2,
            'a' => 1,
            'c' => 3,
        };
        assert!(sut.remove(&'a').is_some());

        assert_eq!(format!("{sut:?}"), r#"{'b': 2, 'c': 3}"#);
    }
}
