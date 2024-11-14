//! # alist
//!
//! `alist` is a Rust crate for working with **association lists**,
//! a simple data structure inspired by Lisp.
//!
//! This implementation is backed by a `Vec` of key-value pairs,
//! preserving the order of insertions and enabling optimized
//! retrieval of items in `O(1)` under certain conditions.
//!
//! ## What is an Association List?
//!
//! An **association list (alist)** is a collection of key-value pairs.
//! It provides a lightweight alternative to hash-based data structures
//! for simple mappings or dictionary-like functionality, especially in
//! contexts where order and immutability are crucial.
//!
//! Like `HashMap`, this implementation does not allow multiple values for the same key,
//! inserting a duplicate key overwrites the existing value.
//!
//! Association lists often outperform hashmaps when working with small datasets, but their performance tends to degrade
//! as the dataset grows larger.
//!
//! This crate mitigates the typical performance drawbacks of association lists on larger datasets by leveraging the
//! stable ordering of items in the list through the Bookmark API.
//!
//! Items in the `alist` are stored in insertion order, which only changes when an element is removed. This property allows
//! the creation of a "bookmark" for an item, significantly improving retrieval times.
//!
//! A bookmark is essentially a record of the item's position in the internal vector. If the item has not been moved,
//! access to it is `O(1)`. If the item has been moved, a linear search is performed, with a worst-case complexity of `O(n)`.
//!
//! These features make `alist` a viable alternative to `HashMap` or `BTreeMap` in scenarios where:
//! - Data removal is infrequent.  
//! - The dataset is small.  
//! - The data type does not implement `Hash` or `Ord`, as this crate only requires items to implement `Eq`.  
//!
//! ### Key Features:
//! - **Order Preservation**: Items are stored in insertion order, which can be essential for certain applications.
//! - **Optimized Retrieval**: By leveraging the sequential nature of the underlying `Vec`, the implementation supports an optimization for retrieving items in `O(1)`.
//! - **Simplicity**: A straightforward design that avoids the overhead of hash-based collections while providing robust functionality.
//!
//! ### Example in Rust:
//! ```rust
//! use alist::AList;
//!
//! let mut alist = AList::new();
//! alist.insert("key1", "value1");
//! alist.insert("key2", "value2");
//!
//! // Linear lookup
//! if let Some(value) = alist.get("key1") {
//!     println!("Found: {}", value);
//! }
//!
//! // Fast lookup
//! let mut k2 = alist.bookmark("key2").unwrap();
//! assert_eq!(alist.get(&mut k2), Some(&"value2"));
//!
//! // Overwriting a value
//! alist.insert("key1", "new_value");
//! assert_eq!(alist.get("key1"), Some(&"new_value"));
//! ```

mod bookmark;
mod entry;
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

use core::borrow::Borrow;
use core::fmt;
use core::hash::{BuildHasher, Hash, Hasher};

use std::collections::hash_map::{DefaultHasher, RandomState};
use std::sync::OnceLock;

/// A association list (alist) implementation, backed by a `Vec` of key-value pairs.
///
/// `AList` preserves the insertion order of elements, making it suitable for scenarios where order matters.
/// It requires keys to implement only the `Eq` trait, providing a simple alternative to `HashMap` or `BTreeMap`.
///
/// ### Features
/// - **Order Preservation**: Items are stored in insertion order, which can be essential for certain applications.
/// - **Optimized Retrieval**: By leveraging the sequential nature of the underlying `Vec`, the implementation supports an optimization for retrieving items in `O(1)`.
/// - **Simplicity**: A straightforward design that avoids the overhead of hash-based collections while providing robust functionality.
///
/// ### Example
/// ```rust
/// use alist::AList;
///
/// let mut alist = AList::new();
/// alist.insert("key1", "value1");
/// alist.insert("key2", "value2");
///
/// assert_eq!(alist.get("key1"), Some(&"value1"));
/// ```
///
/// Use `AList` for small datasets, infrequent removals, or when the data type does not implement `Hash` or `Ord`.
pub struct AList<K, V> {
    pairs: Vec<(K, V)>,
}

impl<K: Eq, V> FromIterator<(K, V)> for AList<K, V> {
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
    /// let alist: AList<&str, &str> = AList::new();
    /// assert!(alist.is_empty());
    /// ```
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
    /// let alist: AList<&str, &str> = AList::with_capacity(10);
    /// assert!(alist.is_empty());
    /// assert!(alist.capacity() >= 10, "Expected the capacity to be at least 10");
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            pairs: Vec::with_capacity(capacity),
        }
    }

    /// Creates a bookmark for the specified key.
    ///
    /// This method allows you to "bookmark" a key in the association list, which can be used for more efficient
    /// retrieval of the corresponding value later. The bookmark stores the position of the key in the internal vector,
    /// and if the item hasn't been moved, retrieving it by this bookmark will be `O(1)`. Otherwise, a linear search is performed.
    /// If the search is performed the bookmark is updated accordingly.
    ///
    /// ### Parameters
    /// - `key`: A reference to the key to bookmark. The key must implement `Borrow<Q>`, and `Q` must implement `Eq`.
    ///
    /// ### Returns
    /// - `Some(Bookmark)` if the key exists in the list, otherwise `None`.
    ///
    /// ### Example
    /// ```rust
    /// use alist::{AList, Bookmark};
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", "value1");
    /// alist.insert("key2", "value2");
    ///
    /// if let Some(mut bookmark) = alist.bookmark("key1") {
    ///     assert_eq!(alist.get(&mut bookmark), Some(&"value1"));
    /// }
    /// ```
    pub fn bookmark<'q, Q>(&self, key: &'q Q) -> Option<Bookmark<'q, Q, K, V>>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
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
    /// - `key`: The key to look up or insert in the `AList`. The key must implement `Eq`.
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
    /// alist.entry("key1").or_insert("value1");
    ///
    /// // Modify the value if the key exists
    /// alist.entry("key1").and_modify(|v| *v = "new_value");
    ///
    /// assert_eq!(alist.get("key1"), Some(&"new_value"));
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<K, V>
    where
        K: Eq,
    {
        if let Some(position) = self.position(&key) {
            return Entry::Occupied(OccupiedEntry::new(self, position));
        }

        Entry::Vacant(VacantEntry::new(self, key))
    }

    /// Inserts a key-value pair into the `AList`.
    ///
    /// If the key already exists in the `AList`, its value is updated to the provided `value`, and the old value is returned.
    /// If the key does not exist, the new pair is appended to the list.
    /// Time complexity is O(n).
    ///
    /// ### Parameters
    /// - `key`: The key to insert or update. Must implement `Eq`.
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
    /// assert!(alist.insert("key1", "value1").is_none());
    ///
    /// // Update an existing key
    /// assert_eq!(alist.insert("key1", "new_value"), Some("value1"));
    ///
    /// // Check the updated value
    /// assert_eq!(alist.get("key1"), Some(&"new_value"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Eq,
    {
        match self.find_mut(&key) {
            Some((_, v)) => Some(std::mem::replace(v, value)),
            None => {
                self.pairs.push((key, value));
                None
            }
        }
    }

    /// Retrieves a reference to the value associated with the given key in the `AList`.
    ///
    /// This method takes any type implementing the `Get<K, V>` trait, enabling flexible key lookups.
    /// If the key exists in the `AList`, a reference to the associated value is returned. Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `Get<K, V>` trait, used to locate the value.
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
    /// alist.insert("key1", "value1");
    ///
    /// // Retrieve a value by key
    /// assert_eq!(alist.get("key1"), Some(&"value1"));
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get("key2").is_none());
    ///
    /// // Retrive a value by its bookmark
    /// let mut k1 = alist.bookmark("key1").unwrap();
    /// assert_eq!(alist.get(&mut k1), Some(&"value1"));
    /// ```
    pub fn get(&self, key: impl Get<K, V>) -> Option<&V> {
        key.get(self)
    }

    /// Retrieves a mutable reference to the value associated with the given key in the `AList`.
    ///
    /// This method takes any type implementing the `GetMut<K, V>` trait, enabling flexible key lookups.
    /// If the key exists in the `AList`, a mutable reference to the associated value is returned. Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `GetMut<K, V>` trait, used to locate the value.
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
    /// alist.insert("key1", "value1");
    ///
    /// // Retrieve a value by key
    /// assert_eq!(alist.get_mut("key1"), Some(&mut "value1"));
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get_mut("key2").is_none());
    ///
    /// // Retrive a value by its bookmark
    /// let mut k1 = alist.bookmark("key1").unwrap();
    /// assert_eq!(alist.get_mut(&mut k1), Some(&mut "value1"));
    /// ```
    pub fn get_mut(&mut self, key: impl GetMut<K, V>) -> Option<&mut V> {
        key.get_mut(self)
    }

    /// Retrieves a reference to the key and its associated value in the `AList`.
    ///
    /// This method takes any type implementing the `GetKeyValue<K, V>` trait, enabling flexible key lookups.
    /// If the key exists in the `AList`, a reference to the key and its associated value is returned as a tuple.
    /// Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `GetKeyValue<K, V>` trait, used to locate the key-value pair.
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
    /// alist.insert("key1", "value1");
    ///
    /// // Retrieve a key-value pair by key
    /// if let Some((k, v)) = alist.get_key_value("key1") {
    ///     assert_eq!(k, &"key1");
    ///     assert_eq!(v, &"value1");
    /// }
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get_key_value("key2").is_none());
    ///
    /// // Retrive a value by its bookmark
    /// let mut k1 = alist.bookmark("key1").unwrap();
    /// assert_eq!(alist.get_key_value(&mut k1), Some((&"key1", &"value1")));
    /// ```
    pub fn get_key_value(&self, key: impl GetKeyValue<K, V>) -> Option<(&K, &V)> {
        key.get_key_value(self)
    }

    /// Retrieves a mutable reference to the key and its associated value in the `AList`.
    ///
    /// This method takes any type implementing the `GetKeyValueMut<K, V>` trait, enabling flexible key lookups.
    /// If the key exists in the `AList`, a reference to the key and its associated mutable value is returned as a tuple.
    /// Otherwise, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `GetKeyValueMut<K, V>` trait, used to locate the key-value pair.
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
    /// alist.insert("key1", "value1");
    ///
    /// // Retrieve a key-value pair by key
    /// if let Some((k, v)) = alist.get_key_value_mut("key1") {
    ///     assert_eq!(k, &"key1");
    ///     assert_eq!(v, &mut "value1");
    /// }
    ///
    /// // Attempt to retrieve a non-existent key
    /// assert!(alist.get_key_value_mut("key2").is_none());
    ///
    /// // Retrive a value by its bookmark
    /// let mut k1 = alist.bookmark("key1").unwrap();
    /// assert_eq!(alist.get_key_value_mut(&mut k1), Some((&"key1", &mut "value1")));
    /// ```
    pub fn get_key_value_mut(&mut self, key: impl GetKeyValueMut<K, V>) -> Option<(&K, &mut V)> {
        key.get_key_value_mut(self)
    }

    /// Checks if the given key exists in the `AList`.
    ///
    /// This method takes any type implementing the `ContainsKey<K, V>` trait, allowing flexible key checks.
    /// It returns `true` if the key is present in the `AList`, and `false` otherwise.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `ContainsKey<K, V>` trait, used to determine if the key exists.
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
    /// alist.insert("key1", "value1");
    ///
    /// // Check for the existence of a key
    /// assert!(alist.contains_key("key1"));
    /// assert!(!alist.contains_key("key2"));
    ///
    /// // Check for the existence of a key by its bookmark
    /// let mut k1 = alist.bookmark("key1").unwrap();
    /// assert!(alist.contains_key(&mut k1));
    /// let mut k2 = Bookmark::new("key2");
    /// assert!(!alist.contains_key(&mut k2));
    /// ```
    pub fn contains_key(&self, key: impl ContainsKey<K, V>) -> bool {
        key.contains_key(self)
    }

    /// Removes a key-value pair from the `AList`.
    ///
    /// This method takes any type implementing the `Remove<K, V>` trait to identify the key to be removed.
    /// If the key exists in the `AList`, the pair is removed, and the associated value is returned.
    /// If the key does not exist, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `Remove<K, V>` trait, used to locate the key-value pair to remove.
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
    /// alist.insert("key1", "value1");
    /// alist.insert("key2", "value2");
    ///
    /// // Remove an existing key
    /// assert_eq!(alist.remove("key1"), Some("value1"));
    /// assert!(!alist.contains_key("key1"));
    ///
    /// // Remove an existing key by its bookmark
    /// let k2 = alist.bookmark("key2").unwrap();
    /// assert_eq!(alist.remove(k2), Some("value2"));
    /// assert!(!alist.contains_key("key2"));
    ///
    /// // Attempt to remove a non-existent key
    /// assert!(alist.remove("key2").is_none());
    /// ```
    pub fn remove(&mut self, key: impl Remove<K, V>) -> Option<V> {
        key.remove(self)
    }

    /// Removes a key-value pair from the `AList` and returns it as a tuple.
    ///
    /// This method takes any type implementing the `RemoveEntry<K, V>` trait to locate the key-value pair to remove.
    /// If the key exists in the `AList`, the pair is removed, and the key and value are returned as a tuple.
    /// If the key does not exist, `None` is returned.
    ///
    /// ### Parameters
    /// - `key`: An input implementing the `RemoveEntry<K, V>` trait, used to locate the key-value pair to remove.
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
    /// alist.insert("key1", "value1");
    /// alist.insert("key2", "value2");
    ///
    /// // Remove an existing key-value pair
    /// assert_eq!(alist.remove_entry("key1"), Some(("key1", "value1")));
    /// assert!(!alist.contains_key("key1"));
    ///
    /// // Remove an existing key-value pair by its bookmark
    /// let k2 = alist.bookmark("key2").unwrap();
    /// assert_eq!(alist.remove_entry(k2), Some(("key2", "value2")));
    /// assert!(!alist.contains_key("key2"));
    ///
    /// // Attempt to remove a non-existent key
    /// assert!(alist.remove_entry("nonexistent").is_none());
    /// ```
    pub fn remove_entry(&mut self, key: impl RemoveEntry<K, V>) -> Option<(K, V)> {
        key.remove_entry(self)
    }

    /// Retains only the key-value pairs in the `AList` that satisfy a predicate.
    ///
    /// This method takes a closure and applies it to each key-value pair in the `AList`.
    /// Only pairs for which the closure returns `true` are kept in the list; others are removed.
    ///
    /// ### Parameters
    /// - `f`: A closure of the form `FnMut(&K, &mut V) -> bool`, applied to each key-value pair.
    ///        If the closure returns `true`, the pair is retained; otherwise, it is removed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    /// alist.insert("key3", 3);
    ///
    /// // Retain only pairs where the value is greater than 1
    /// alist.retain(|_, v| *v > 1);
    ///
    /// assert!(!alist.contains_key("key1"));
    /// assert!(alist.contains_key("key2"));
    /// assert!(alist.contains_key("key3"));
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
    ///        If the closure returns `true`, the pair is retained; otherwise, it is removed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    /// alist.insert("key3", 3);
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
    /// assert_eq!(alist.get("key1"), Some(&2));
    /// assert!(!alist.contains_key("key2"));
    /// assert_eq!(alist.get("key3"), Some(&6));
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.pairs.retain_mut(|(k, v)| f(k, v));
    }

    fn position<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.pairs.iter().position(|(k, _)| k.borrow() == key)
    }

    fn find<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.pairs
            .iter()
            .find(|(k, _)| k.borrow() == key)
            .map(|(k, v)| (k, v))
    }

    fn find_mut<Q>(&mut self, key: &Q) -> Option<(&K, &mut V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.pairs
            .iter_mut()
            .find(|(k, _)| k.borrow() == key)
            .map(|(k, v)| (&*k, v))
    }

    fn is_valid<Q>(&self, bookmark: &Bookmark<Q, K, V>) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.pairs
            .get(bookmark.position)
            .map(|(k, _)| k.borrow() == bookmark.key())
            .unwrap_or(false)
    }
}

impl<K: Eq, V> Extend<(K, V)> for AList<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let pairs = iter.into_iter();

        let (lower, upper) = pairs.size_hint();
        self.reserve(usize::min(upper.unwrap_or(lower), 8));

        for (key, value) in pairs {
            match self.find_mut(&key) {
                None => self.pairs.push((key, value)),
                Some((_, v)) => *v = value,
            }
        }
    }
}

impl<'a, K: Eq + Clone, V: Clone> Extend<(&'a K, &'a V)> for AList<K, V> {
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
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
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
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
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
    /// let mut alist: AList<&str, i32> = AList::new();
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
    /// let mut alist: AList<&str, i32> = AList::new();
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
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    /// assert!(alist.capacity() >= 2); // Capacity is greater than or equal to the number of inserted elements.
    /// ```
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
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    /// assert_eq!(alist.len(), 2);
    /// ```
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

    /// alist.insert("key1", 1);
    /// assert!(!alist.is_empty());

    /// alist.clear();
    /// assert!(alist.is_empty());
    /// ```
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
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
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
    /// The keys are yielded in the order they were inserted, and the iterator will not modify the list.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// let keys: Vec<_> = alist.keys().collect();
    /// assert_eq!(&keys[..], &[&"key1", &"key2"]);
    /// ```
    pub fn keys(&self) -> Keys<K, V> {
        Keys::from_delegate(self.pairs.iter())
    }

    /// Consumes the `AList` and returns an iterator over the keys.
    ///
    /// This method consumes the `AList` and returns an iterator that yields the keys of the key-value pairs in the order
    /// they were inserted. After calling `into_keys`, the `AList` is no longer accessible as it has been consumed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// let keys: Vec<_> = alist.into_keys().collect();
    /// assert_eq!(keys, vec!["key1", "key2"]);
    /// ```
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys::from_delegate(self.pairs.into_iter())
    }

    /// Returns an iterator over the values of the `AList`.
    ///
    /// This method returns an iterator that yields references to the values of the key-value pairs stored in the `AList`.
    /// The values are yielded in the order they were inserted, and the iterator will not modify the list.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// let values: Vec<_> = alist.values().collect();
    /// assert_eq!(values, vec![&1, &2]);
    /// ```
    pub fn values(&self) -> Values<K, V> {
        Values::from_delegate(self.pairs.iter())
    }

    /// Returns a mutable iterator over the values of the `AList`.
    ///
    /// This method returns a mutable iterator that allows modifying the values of the key-value pairs stored in the `AList`.
    /// The values are yielded in the order they were inserted, and the iterator will not modify the structure of the list.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// for value in alist.values_mut() {
    ///     *value *= 2;  // Doubling each value
    /// }
    ///
    /// let values: Vec<_> = alist.values().collect();
    /// assert_eq!(&values[..], &[&2, &4]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut::from_delegate(self.pairs.iter_mut())
    }

    /// Consumes the `AList` and returns an iterator over the values.
    ///
    /// This method consumes the `AList` and returns an iterator that yields the values of the key-value pairs in the order
    /// they were inserted. After calling `into_values`, the `AList` is no longer accessible as it has been consumed.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// let values: Vec<_> = alist.into_values().collect();
    /// assert_eq!(values, vec![1, 2]);
    /// ```
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues::from_delegate(self.pairs.into_iter())
    }

    /// Returns an iterator over the key-value pairs of the `AList`.
    ///
    /// This method returns an iterator that yields references to the key-value pairs stored in the `AList` in the order
    /// they were inserted. The iterator allows read-only access to both the keys and values.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// let pairs: Vec<_> = alist.iter().collect();
    /// assert_eq!(&pairs[..], &[(&"key1", &1), (&"key2", &2)]);
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter::from_delegate(self.pairs.iter())
    }

    /// Returns a mutable iterator over the key-value pairs of the `AList`.
    ///
    /// This method returns a mutable iterator that allows modifying both the keys and values of the key-value pairs stored
    /// in the `AList`. The iterator yields the key-value pairs in the order they were inserted.
    ///
    /// ### Example
    /// ```rust
    /// use alist::AList;
    ///
    /// let mut alist = AList::new();
    /// alist.insert("key1", 1);
    /// alist.insert("key2", 2);
    ///
    /// for (_key, value) in alist.iter_mut() {
    ///     *value *= 2;  // Doubling each value
    /// }
    ///
    /// let values: Vec<_> = alist.values().collect();
    /// assert_eq!(&values[..], &[&2, &4]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map = f.debug_map();
        self.pairs.iter().for_each(|(k, v)| {
            map.entry(k, v);
        });
        map.finish()
    }
}

impl<K: Eq, V: PartialEq> PartialEq for AList<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|(k, v)| other.get(k).filter(|w| v == *w).is_some())
    }
}

impl<K: Eq, V: Eq> Eq for AList<K, V> {}

impl<K: Hash, V: Hash> Hash for AList<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let hasher_builder = global_hasher_builder();
        let hash = self
            .values()
            .map(|p| hasher_builder.hash_one(p))
            .fold(hasher_builder.hash_one(self.len()), |l, r| l ^ r);

        state.write_usize(self.len());
        state.write_u64(hash);
    }
}

fn global_hasher_builder() -> &'static impl BuildHasher<Hasher = DefaultHasher> {
    static INSTANCE: OnceLock<RandomState> = OnceLock::new();
    INSTANCE.get_or_init(RandomState::new)
}

#[cfg(test)]
mod tests {
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};

    use crate::{alist, AList, Bookmark};

    #[test]
    fn alist_macro() {
        let sut = alist! {
            "k1" => "v1",
            "k2" => "v2",
            "k1" => "w1",
        };

        assert_eq!(
            sut.into_iter().collect::<Vec<_>>(),
            [("k1", "w1"), ("k2", "v2")]
        );
    }

    #[test]
    fn hash() {
        let symbols = ["x", "y", "z"];
        let values = [1, 2, 3];

        let mut pairs = symbols
            .into_iter()
            .zip(values.into_iter())
            .collect::<Vec<_>>();

        let mut l = pairs.iter().cloned().collect::<AList<_, _>>();

        pairs.swap(0, 2);
        let mut r = pairs.into_iter().collect::<AList<_, _>>();

        assert_eq!(l, r);

        let hasher_builder = BuildHasherDefault::<DefaultHasher>::default();
        let (h1, h2) = (hasher_builder.hash_one(&l), hasher_builder.hash_one(&r));
        assert_eq!(h1, h2);

        r.remove("x");
        let (h1, h2) = (hasher_builder.hash_one(&l), hasher_builder.hash_one(&r));
        assert_ne!(h1, h2);

        l.remove("x");
        let (h1, h2) = (hasher_builder.hash_one(&l), hasher_builder.hash_one(&r));
        assert_eq!(h1, h2);
    }

    #[test]
    fn new_creates_empty_alist() {
        let sut: AList<&str, &str> = AList::new();
        assert!(sut.is_empty(), "Expected the alist to be empty");
        assert_eq!(sut.len(), 0, "Expected the length of the alist to be 0");
    }

    #[test]
    fn default_creates_empty_alist() {
        let sut: AList<&str, &str> = AList::default();
        assert!(sut.is_empty(), "Expected the alist to be empty");
        assert_eq!(sut.len(), 0, "Expected the length of the alist to be 0");
    }

    #[test]
    fn with_capacity_creates_alist_with_specified_capacity() {
        let capacity = 10;
        let sut: AList<&str, &str> = AList::with_capacity(capacity);
        assert!(sut.is_empty(), "Expected the alist to be empty");
        assert!(
            sut.capacity() >= capacity,
            "Expected the alist to have a capacity of at least {}",
            capacity
        );
    }

    #[test]
    fn bookmark_creates_valid_bookmark() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Create a bookmark for "key1"
        if let Some(mut bookmark) = sut.bookmark("key1") {
            assert_eq!(sut.get(&mut bookmark), Some(&"value1"));
        } else {
            panic!("Expected bookmark to be created for 'key1'");
        }
    }

    #[test]
    fn bookmark_returns_none_for_nonexistent_key() {
        let sut: AList<&str, &str> = AList::new();

        // Try creating a bookmark for a non-existent key
        assert!(
            sut.bookmark("nonexistent").is_none(),
            "Expected None for nonexistent key"
        );
    }

    #[test]
    fn entry_insert_new_key() {
        let mut sut = AList::new();

        // Insert a new key-value pair
        sut.entry("key1").or_insert("value1");

        assert_eq!(
            sut.get("key1"),
            Some(&"value1"),
            "Expected 'key1' to be inserted with 'value1'"
        );
    }

    #[test]
    fn entry_modify_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Modify the value of an existing key
        sut.entry("key1").and_modify(|v| *v = "new_value");

        assert_eq!(
            sut.get("key1"),
            Some(&"new_value"),
            "Expected 'key1' to have its value updated to 'new_value'"
        );
    }

    #[test]
    fn entry_insert_if_not_exists() {
        let mut sut = AList::new();

        // Insert a value if the key doesn't exist
        sut.entry("key1").or_insert("value1");

        // Ensure the value is not overwritten for an existing key
        sut.entry("key1").or_insert("other_value");

        assert_eq!(
            sut.get("key1"),
            Some(&"value1"),
            "Expected 'key1' to remain 'value1' after re-insertion attempt"
        );
    }

    #[test]
    fn insert_new_key() {
        let mut sut = AList::new();

        // Insert a new key-value pair
        let result = sut.insert("key1", "value1");
        assert!(result.is_none(), "Expected None for a new key insertion");
        assert_eq!(
            sut.get("key1"),
            Some(&"value1"),
            "Expected 'key1' to map to 'value1'"
        );
    }

    #[test]
    fn insert_update_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Update the value for an existing key
        let result = sut.insert("key1", "new_value");
        assert_eq!(
            result,
            Some("value1"),
            "Expected 'value1' as the previous value"
        );
        assert_eq!(
            sut.get("key1"),
            Some(&"new_value"),
            "Expected 'key1' to map to 'new_value'"
        );
    }

    #[test]
    fn insert_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Verify both keys are present
        assert_eq!(
            sut.get("key1"),
            Some(&"value1"),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get("key2"),
            Some(&"value2"),
            "Expected 'key2' to map to 'value2'"
        );
    }

    #[test]
    fn get_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Retrieve an existing key
        let result = sut.get("key1");
        assert_eq!(
            result,
            Some(&"value1"),
            "Expected to retrieve 'value1' for 'key1'"
        );

        // Retrieve an existing key by its bookmark
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let result = sut.get(&mut k1);
        assert_eq!(
            result,
            Some(&"value1"),
            "Expected to retrieve 'value1' for 'key1'"
        );
    }

    #[test]
    fn get_nonexistent_key() {
        let sut: AList<&str, &str> = AList::new();

        // Attempt to retrieve a non-existent key
        let result = sut.get("nonexistent");
        assert!(result.is_none(), "Expected None for a non-existent key");

        // Attempt to retrieve a non-existent key from its bookmark
        let mut bookmark = Bookmark::new("nonexistent");
        let result = sut.get(&mut bookmark);
        assert!(result.is_none(), "Expected None for a non-existent key");
    }

    #[test]
    fn get_with_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Retrieve values for multiple keys
        assert_eq!(
            sut.get("key1"),
            Some(&"value1"),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get("key2"),
            Some(&"value2"),
            "Expected 'key2' to map to 'value2'"
        );

        // Retrieve values for multiple keys by their bookmarks
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let mut k2 = Bookmark::new("key2");
        assert_eq!(
            sut.get(&mut k1),
            Some(&"value1"),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get(&mut k2),
            Some(&"value2"),
            "Expected 'key2' to map to 'value2'"
        );
    }

    #[test]
    fn get_mut_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Retrieve an existing key
        let result = sut.get_mut("key1");
        assert_eq!(
            result,
            Some(&mut "value1"),
            "Expected to retrieve 'value1' for 'key1'"
        );

        // Retrieve an existing key by its bookmark
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let result = sut.get_mut(&mut k1);
        assert_eq!(
            result,
            Some(&mut "value1"),
            "Expected to retrieve 'value1' for 'key1'"
        );
    }

    #[test]
    fn get_mut_nonexistent_key() {
        let mut sut: AList<&str, &str> = AList::new();

        // Attempt to retrieve a non-existent key
        let result = sut.get_mut("nonexistent");
        assert!(result.is_none(), "Expected None for a non-existent key");

        // Attempt to retrieve a non-existent key from its bookmark
        let mut bookmark = Bookmark::new("nonexistent");
        let result = sut.get_mut(&mut bookmark);
        assert!(result.is_none(), "Expected None for a non-existent key");
    }

    #[test]
    fn get_mut_with_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Retrieve values for multiple keys
        assert_eq!(
            sut.get_mut("key1"),
            Some(&mut "value1"),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get_mut("key2"),
            Some(&mut "value2"),
            "Expected 'key2' to map to 'value2'"
        );

        // Retrieve values for multiple keys by their bookmarks
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let mut k2 = Bookmark::new("key2");
        assert_eq!(
            sut.get_mut(&mut k1),
            Some(&mut "value1"),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get_mut(&mut k2),
            Some(&mut "value2"),
            "Expected 'key2' to map to 'value2'"
        );
    }

    #[test]
    fn get_key_value_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Retrieve an existing key-value pair
        if let Some((key, value)) = sut.get_key_value("key1") {
            assert_eq!(key, &"key1", "Expected 'key1' as the retrieved key");
            assert_eq!(value, &"value1", "Expected 'value1' as the retrieved value");
        } else {
            panic!("Expected to retrieve key-value pair for 'key1'");
        }

        // Retrieve an existing key-value pair by its bookmark
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        if let Some((key, value)) = sut.get_key_value(&mut k1) {
            assert_eq!(key, &"key1", "Expected 'key1' as the retrieved key");
            assert_eq!(value, &"value1", "Expected 'value1' as the retrieved value");
        } else {
            panic!("Expected to retrieve key-value pair for 'key1'");
        }
    }

    #[test]
    fn get_key_value_nonexistent_key() {
        let sut: AList<&str, &str> = AList::new();

        // Attempt to retrieve a non-existent key
        let result = sut.get_key_value("nonexistent");
        assert!(result.is_none(), "Expected None for a non-existent key");

        // Attempt to retrieve a non-existent key from its bookmark
        let mut bookmark = Bookmark::new("nonexistent");
        let result = sut.get_key_value(&mut bookmark);
        assert!(result.is_none(), "Expected None for a non-existent key");
    }

    #[test]
    fn get_key_value_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Retrieve key-value pairs for multiple keys
        if let Some((key, value)) = sut.get_key_value("key1") {
            assert_eq!(key, &"key1", "Expected 'key1' as the retrieved key");
            assert_eq!(value, &"value1", "Expected 'value1' as the retrieved value");
        }

        if let Some((key, value)) = sut.get_key_value("key2") {
            assert_eq!(key, &"key2", "Expected 'key2' as the retrieved key");
            assert_eq!(value, &"value2", "Expected 'value2' as the retrieved value");
        }

        // Retrievekey-value pairs for multiple keys by their bookmarks
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let mut k2 = Bookmark::new("key2");
        assert_eq!(
            sut.get_key_value(&mut k1),
            Some((&"key1", &"value1")),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get_key_value(&mut k2),
            Some((&"key2", &"value2")),
            "Expected 'key2' to map to 'value2'"
        );
    }

    #[test]
    fn get_key_value_mut_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Retrieve an existing key-value pair
        if let Some((key, value)) = sut.get_key_value_mut("key1") {
            assert_eq!(key, &"key1", "Expected 'key1' as the retrieved key");
            assert_eq!(value, &"value1", "Expected 'value1' as the retrieved value");
        } else {
            panic!("Expected to retrieve key-value pair for 'key1'");
        }

        // Retrieve an existing key-value pair by its bookmark
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        if let Some((key, value)) = sut.get_key_value_mut(&mut k1) {
            assert_eq!(key, &"key1", "Expected 'key1' as the retrieved key");
            assert_eq!(value, &"value1", "Expected 'value1' as the retrieved value");
        } else {
            panic!("Expected to retrieve key-value pair for 'key1'");
        }
    }

    #[test]
    fn get_key_value_mut_nonexistent_key() {
        let mut sut: AList<&str, &str> = AList::new();

        // Attempt to retrieve a non-existent key
        let result = sut.get_key_value_mut("nonexistent");
        assert!(result.is_none(), "Expected None for a non-existent key");

        // Attempt to retrieve a non-existent key from its bookmark
        let mut bookmark = Bookmark::new("nonexistent");
        let result = sut.get_key_value_mut(&mut bookmark);
        assert!(result.is_none(), "Expected None for a non-existent key");
    }

    #[test]
    fn get_key_value_mut_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Retrieve key-value pairs for multiple keys
        if let Some((key, value)) = sut.get_key_value_mut("key1") {
            assert_eq!(key, &"key1", "Expected 'key1' as the retrieved key");
            assert_eq!(value, &"value1", "Expected 'value1' as the retrieved value");
        }

        if let Some((key, value)) = sut.get_key_value_mut("key2") {
            assert_eq!(key, &"key2", "Expected 'key2' as the retrieved key");
            assert_eq!(value, &"value2", "Expected 'value2' as the retrieved value");
        }

        // Retrievekey-value pairs for multiple keys by their bookmarks
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let mut k2 = Bookmark::new("key2");
        assert_eq!(
            sut.get_key_value_mut(&mut k1),
            Some((&"key1", &mut "value1")),
            "Expected 'key1' to map to 'value1'"
        );
        assert_eq!(
            sut.get_key_value_mut(&mut k2),
            Some((&"key2", &mut "value2")),
            "Expected 'key2' to map to 'value2'"
        );
    }

    #[test]
    fn contains_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");

        // Check for an existing key
        assert!(
            sut.contains_key("key1"),
            "Expected 'key1' to exist in the list"
        );

        // Check for an existing key by its bookmark
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        assert!(sut.contains_key(&mut k1));
    }

    #[test]
    fn contains_nonexistent_key() {
        let sut: AList<&str, &str> = AList::new();

        // Check for a non-existent key
        assert!(
            !sut.contains_key("nonexistent"),
            "Expected 'nonexistent' to not exist in the list"
        );

        // Check for an non-existent key by its bookmark
        let mut bookmark = Bookmark::new("nonexistent");
        assert!(
            !sut.contains_key(&mut bookmark),
            "Expected 'nonexistent' to not exist in the list"
        );
    }

    #[test]
    fn contains_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Check for multiple keys
        assert!(
            sut.contains_key("key1"),
            "Expected 'key1' to exist in the list"
        );
        assert!(
            sut.contains_key("key2"),
            "Expected 'key2' to exist in the list"
        );
        assert!(
            !sut.contains_key("key3"),
            "Expected 'key3' to not exist in the list"
        );

        // Check for multiple keys by their bookmarks
        let mut k1 = sut
            .bookmark("key1")
            .expect("Expected a valid bookmark for 'key1'");
        let mut k2 = Bookmark::new("key2");
        let mut k3 = Bookmark::new("key3");
        assert!(
            sut.contains_key(&mut k1),
            "Expected 'key1' to exist in the list"
        );
        assert!(
            sut.contains_key(&mut k2),
            "Expected 'key2' to exist in the list"
        );
        assert!(
            !sut.contains_key(&mut k3),
            "Expected 'key3' to not exist in the list"
        );
    }

    #[test]
    fn remove_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Remove an existing key
        let result = sut.remove("key1");
        assert_eq!(
            result,
            Some("value1"),
            "Expected to remove 'key1' with value 'value1'"
        );
        assert!(
            !sut.contains_key("key1"),
            "Expected 'key1' to be removed from the list"
        );

        // Remove an existing key by its bookmark
        let k2 = sut
            .bookmark("key2")
            .expect("Expected a valid bookmark for 'key2'");
        let result = sut.remove(k2);
        assert_eq!(
            result,
            Some("value2"),
            "Expected to remove 'key2' with value 'value2'"
        );
        assert!(
            !sut.contains_key("key2"),
            "Expected 'key2' to be removed from the list"
        );
    }

    #[test]
    fn remove_nonexistent_key() {
        let mut sut: AList<&str, &str> = AList::new();

        // Attempt to remove a non-existent key
        let result = sut.remove("nonexistent");
        assert!(
            result.is_none(),
            "Expected None when attempting to remove a non-existent key"
        );

        // Attempt to remove a non-existent key by its bookmark
        let bookmark = Bookmark::new("nonexistent");
        let result = sut.remove(bookmark);
        assert!(
            result.is_none(),
            "Expected None when attempting to remove a non-existent key"
        );
    }

    #[test]
    fn remove_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");
        sut.insert("key3", "value3");
        sut.insert("key4", "value4");

        // Remove multiple keys
        assert_eq!(
            sut.remove("key1"),
            Some("value1"),
            "Expected to remove 'key1' with value 'value1'"
        );
        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");

        assert_eq!(
            sut.remove("key2"),
            Some("value2"),
            "Expected to remove 'key2' with value 'value2'"
        );
        assert!(!sut.contains_key("key2"), "Expected 'key2' to be removed");

        // Remove multiple keys by their bookmarks
        let k3 = sut
            .bookmark("key3")
            .expect("Expected a valid bookmark for 'key3'");
        let k4 = Bookmark::new("key4");

        assert_eq!(
            sut.remove(k3),
            Some("value3"),
            "Expected to remove 'key3' with value 'value3'"
        );
        assert!(!sut.contains_key("key3"), "Expected 'key3' to be removed");

        assert_eq!(
            sut.remove(k4),
            Some("value4"),
            "Expected to remove 'key4' with value 'value4'"
        );
        assert!(!sut.contains_key("key4"), "Expected 'key4' to be removed");
    }

    #[test]
    fn remove_entry_existing_key() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");

        // Remove an existing key-value pair
        let result = sut.remove_entry("key1");
        assert_eq!(
            result,
            Some(("key1", "value1")),
            "Expected to remove 'key1' with value 'value1'"
        );
        assert!(
            !sut.contains_key("key1"),
            "Expected 'key1' to be removed from the list"
        );

        // Remove an existing key-value pair by its bookmark
        let k2 = sut.bookmark("key2").unwrap();
        let result = sut.remove_entry(k2);
        assert_eq!(
            result,
            Some(("key2", "value2")),
            "Expected to remove 'key2' with value 'value2'"
        );
        assert!(
            !sut.contains_key("key2"),
            "Expected 'key2' to be removed from the list"
        );
    }

    #[test]
    fn remove_entry_nonexistent_key() {
        let mut sut: AList<&str, &str> = AList::new();

        // Attempt to remove a non-existent key
        let result = sut.remove_entry("nonexistent");
        assert!(
            result.is_none(),
            "Expected None when attempting to remove a non-existent key"
        );

        // Attempt to remove a non-existent key by its bookmark
        let bookmark = Bookmark::new("nonexistent");
        let result = sut.remove_entry(bookmark);
        assert!(
            result.is_none(),
            "Expected None when attempting to remove a non-existent key"
        );
    }

    #[test]
    fn remove_entry_multiple_keys() {
        let mut sut = AList::new();
        sut.insert("key1", "value1");
        sut.insert("key2", "value2");
        sut.insert("key3", "value3");
        sut.insert("key4", "value4");

        // Remove multiple key-value pairs
        assert_eq!(
            sut.remove_entry("key1"),
            Some(("key1", "value1")),
            "Expected to remove 'key1' with value 'value1'"
        );
        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");

        assert_eq!(
            sut.remove_entry("key2"),
            Some(("key2", "value2")),
            "Expected to remove 'key2' with value 'value2'"
        );
        assert!(!sut.contains_key("key2"), "Expected 'key2' to be removed");

        // Remove multiple key-value pairs by their bookmarks
        let k3 = sut
            .bookmark("key3")
            .expect("Expected a valid bookmark for 'key3'");
        let k4 = Bookmark::new("key4");

        assert_eq!(
            sut.remove_entry(k3),
            Some(("key3", "value3")),
            "Expected to remove 'key3' with value 'value3'"
        );
        assert!(!sut.contains_key("key3"), "Expected 'key3' to be removed");

        assert_eq!(
            sut.remove_entry(k4),
            Some(("key4", "value4")),
            "Expected to remove 'key4' with value 'value4'"
        );
        assert!(!sut.contains_key("key4"), "Expected 'key4' to be removed");
    }

    #[test]
    fn retain_some_pairs() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        sut.insert("key3", 3);

        // Retain only pairs where the value is greater than 1
        sut.retain(|_, v| *v > 1);

        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");
        assert!(sut.contains_key("key2"), "Expected 'key2' to be retained");
        assert!(sut.contains_key("key3"), "Expected 'key3' to be retained");
    }

    #[test]
    fn retain_all_pairs() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Retain all pairs
        sut.retain(|_, _| true);

        assert!(sut.contains_key("key1"), "Expected 'key1' to be retained");
        assert!(sut.contains_key("key2"), "Expected 'key2' to be retained");
    }

    #[test]
    fn retain_no_pairs() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Remove all pairs
        sut.retain(|_, _| false);

        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");
        assert!(!sut.contains_key("key2"), "Expected 'key2' to be removed");
    }

    #[test]
    fn retain_based_on_keys() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        sut.insert("key3", 3);

        // Retain only pairs with keys starting with 'key2'
        sut.retain(|k, _| *k == "key2");

        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");
        assert!(sut.contains_key("key2"), "Expected 'key2' to be retained");
        assert!(!sut.contains_key("key3"), "Expected 'key3' to be removed");
    }

    #[test]
    fn retain_mut_some_pairs() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        sut.insert("key3", 3);

        // Retain pairs with even values and double their values
        sut.retain_mut(|_, v| {
            if *v % 2 == 0 {
                *v *= 2;
                true
            } else {
                false
            }
        });

        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");
        assert_eq!(
            sut.get("key2"),
            Some(&4),
            "Expected 'key2' to be retained and doubled"
        );
        assert!(!sut.contains_key("key3"), "Expected 'key3' to be removed");
    }

    #[test]
    fn retain_mut_all_pairs() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Retain all pairs and increment their values
        sut.retain_mut(|_, v| {
            *v += 1;
            true
        });

        assert_eq!(
            sut.get("key1"),
            Some(&2),
            "Expected 'key1' to be retained and incremented"
        );
        assert_eq!(
            sut.get("key2"),
            Some(&3),
            "Expected 'key2' to be retained and incremented"
        );
    }

    #[test]
    fn retain_mut_no_pairs() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Remove all pairs
        sut.retain_mut(|_, _| false);

        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");
        assert!(!sut.contains_key("key2"), "Expected 'key2' to be removed");
    }

    #[test]
    fn retain_mut_based_on_keys() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        sut.insert("key3", 3);

        // Retain only pairs with keys starting with 'key2' and increment their values
        sut.retain_mut(|k, v| {
            if *k == "key2" {
                *v += 1;
                true
            } else {
                false
            }
        });

        assert!(!sut.contains_key("key1"), "Expected 'key1' to be removed");
        assert_eq!(
            sut.get("key2"),
            Some(&3),
            "Expected 'key2' to be retained and incremented"
        );
        assert!(!sut.contains_key("key3"), "Expected 'key3' to be removed");
    }

    #[test]
    fn extend_with_new_items() {
        let mut sut = AList::new();

        let new_items = vec![("key1", 1), ("key2", 2), ("key3", 3)];
        sut.extend(new_items);

        assert_eq!(sut.get("key1"), Some(&1), "Expected 'key1' to have value 1");
        assert_eq!(sut.get("key2"), Some(&2), "Expected 'key2' to have value 2");
        assert_eq!(sut.get("key3"), Some(&3), "Expected 'key3' to have value 3");
    }

    #[test]
    fn extend_with_replacing_items() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let new_items = vec![("key2", 20), ("key3", 30)];
        sut.extend(new_items);

        assert_eq!(
            sut.get("key1"),
            Some(&1),
            "Expected 'key1' to retain value 1"
        );
        assert_eq!(
            sut.get("key2"),
            Some(&20),
            "Expected 'key2' to be replaced with value 20"
        );
        assert_eq!(
            sut.get("key3"),
            Some(&30),
            "Expected 'key3' to be inserted with value 30"
        );
    }

    #[test]
    fn extend_with_empty_iterator() {
        let mut sut = AList::new();
        sut.insert("key1", 1);

        sut.extend(Vec::<(&str, i32)>::new());

        assert_eq!(
            sut.get("key1"),
            Some(&1),
            "Expected 'key1' to remain unchanged"
        );
        assert_eq!(sut.len(), 1, "Expected the AList to contain one item");
    }

    #[test]
    fn extend_with_duplicate_keys() {
        let mut sut = AList::new();
        sut.insert("key1", 1);

        let new_items = vec![("key1", 10), ("key1", 20)];
        sut.extend(new_items);

        assert_eq!(
            sut.get("key1"),
            Some(&20),
            "Expected 'key1' to have the last inserted value 20"
        );
    }

    #[test]
    fn extend_with_ref_items() {
        let mut sut: AList<&str, i32> = AList::new();

        let new_items = [(&"key1", &1), (&"key2", &2), (&"key3", &3)];
        sut.extend(new_items);

        assert_eq!(sut.get("key1"), Some(&1), "Expected 'key1' to have value 1");
        assert_eq!(sut.get("key2"), Some(&2), "Expected 'key2' to have value 2");
        assert_eq!(sut.get("key3"), Some(&3), "Expected 'key3' to have value 3");
    }

    #[test]
    fn shrink_to_fit_reduces_capacity() {
        let mut sut = AList::with_capacity(100);
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let old_capacity = sut.capacity();
        assert!(
            old_capacity >= 100,
            "Expected initial capacity to be at least 100"
        );

        sut.shrink_to_fit();
        let new_capacity = sut.capacity();

        assert!(
            new_capacity >= sut.len(),
            "Expected capacity to be no less than length"
        );
        assert!(
            new_capacity <= old_capacity,
            "Expected capacity to be reduced"
        );
    }

    #[test]
    fn shrink_to_fit_no_effect_when_exact_capacity() {
        let mut sut = AList::with_capacity(2);
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let old_capacity = sut.capacity();
        sut.shrink_to_fit();
        let new_capacity = sut.capacity();

        assert_eq!(
            new_capacity, old_capacity,
            "Expected capacity to remain unchanged"
        );
    }

    #[test]
    fn shrink_to_reduces_capacity() {
        let mut sut = AList::with_capacity(100);
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let old_capacity = sut.capacity();
        assert!(
            old_capacity >= 100,
            "Expected initial capacity to be at least 100"
        );

        sut.shrink_to(10);
        let new_capacity = sut.capacity();

        assert!(
            new_capacity >= 10,
            "Expected capacity to be no less than the specified minimum"
        );
        assert!(
            new_capacity <= old_capacity,
            "Expected capacity to be reduced"
        );
    }

    #[test]
    fn shrink_to_no_effect_when_below_length() {
        let mut sut = AList::with_capacity(2);
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let old_capacity = sut.capacity();
        sut.shrink_to(1);
        let new_capacity = sut.capacity();

        assert_eq!(
            new_capacity, old_capacity,
            "Expected capacity to remain unchanged"
        );
    }

    #[test]
    fn shrink_to_exact_length() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        sut.shrink_to(sut.len());
        let new_capacity = sut.capacity();

        assert_eq!(
            new_capacity,
            sut.len(),
            "Expected capacity to match the length of the AList"
        );
    }

    #[test]
    fn reserve_increases_capacity_when_needed() {
        let mut sut: AList<&str, i32> = AList::new();
        let initial_capacity = sut.capacity();

        sut.reserve(100);
        assert!(
            sut.capacity() >= 100,
            "Expected capacity to be at least 100"
        );
        assert!(
            sut.capacity() > initial_capacity,
            "Expected capacity to increase"
        );
    }

    #[test]
    fn reserve_does_not_increase_capacity_if_sufficient() {
        let mut sut: AList<&str, i32> = AList::with_capacity(100);
        let initial_capacity = sut.capacity();

        sut.reserve(10);
        assert_eq!(
            sut.capacity(),
            initial_capacity,
            "Expected capacity to remain unchanged"
        );
    }

    #[test]
    fn reserve_does_not_increase_capacity_for_zero() {
        let mut sut: AList<&str, i32> = AList::new();
        let initial_capacity = sut.capacity();

        sut.reserve(0);
        assert_eq!(
            sut.capacity(),
            initial_capacity,
            "Expected capacity to remain unchanged"
        );
    }

    #[test]
    fn reserve_exact_increases_capacity_when_needed() {
        let mut sut: AList<&str, i32> = AList::new();
        let initial_capacity = sut.capacity();

        sut.reserve_exact(100);
        assert!(
            sut.capacity() >= 100,
            "Expected capacity to be at least 100"
        );
        assert!(
            sut.capacity() > initial_capacity,
            "Expected capacity to increase"
        );
    }

    #[test]
    fn reserve_exact_does_not_increase_capacity_if_sufficient() {
        let mut sut: AList<&str, i32> = AList::with_capacity(100);
        let initial_capacity = sut.capacity();

        sut.reserve_exact(10);
        assert_eq!(
            sut.capacity(),
            initial_capacity,
            "Expected capacity to remain unchanged"
        );
    }

    #[test]
    fn reserve_exact_does_not_increase_capacity_for_zero() {
        let mut sut: AList<&str, i32> = AList::new();
        let initial_capacity = sut.capacity();

        sut.reserve_exact(0);
        assert_eq!(
            sut.capacity(),
            initial_capacity,
            "Expected capacity to remain unchanged"
        );
    }

    #[test]
    fn clear_removes_all_elements() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        assert_eq!(sut.len(), 2);

        sut.clear();
        assert_eq!(sut.len(), 0);
        assert!(sut.is_empty(), "Expected AList to be empty after clear");
    }

    #[test]
    fn clear_leaves_capacity_untouched() {
        let mut sut = AList::with_capacity(100);
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        let old_capacity = sut.capacity();

        sut.clear();
        assert_eq!(sut.len(), 0);
        assert!(
            sut.capacity() >= old_capacity,
            "Expected capacity to remain the same after clear"
        );
    }

    #[test]
    fn capacity_increases_with_insertions() {
        let mut sut = AList::new();
        let initial_capacity = sut.capacity();

        sut.insert("key1", 1);
        sut.insert("key2", 2);
        assert!(
            sut.capacity() >= initial_capacity,
            "Expected capacity to be at least 2 after insertions"
        );

        // After removing elements, the capacity shouldn't shrink unless manually changed (e.g., via shrink_to_fit)
        sut.remove("key1");
        assert!(
            sut.capacity() >= 2,
            "Expected capacity to remain the same after removal"
        );
    }

    #[test]
    fn capacity_does_not_decrease_after_clear() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);
        let current_capacity = sut.capacity();

        sut.clear();
        assert_eq!(sut.len(), 0);
        assert!(
            sut.capacity() >= current_capacity,
            "Expected capacity to remain unchanged after clear"
        );
    }

    #[test]
    fn capacity_after_reserve() {
        let mut sut: AList<&str, i32> = AList::new();
        let initial_capacity = sut.capacity();

        sut.reserve(100);
        assert!(
            sut.capacity() >= 100,
            "Expected capacity to increase after reserve"
        );
        assert!(
            sut.capacity() > initial_capacity,
            "Expected capacity to increase after reserve"
        );
    }

    #[test]
    fn capacity_does_not_increase_with_zero_insertions() {
        let mut sut = alist! {
            "key1" => 1,
        };
        let initial_capacity = sut.capacity();

        sut.remove("key1");

        assert_eq!(
            sut.capacity(),
            initial_capacity,
            "Expected capacity to remain the same after no insertions"
        );
    }

    #[test]
    fn len_returns_correct_number_of_elements() {
        let mut sut = AList::new();
        assert_eq!(sut.len(), 0);

        sut.insert("key1", 1);
        sut.insert("key2", 2);
        assert_eq!(sut.len(), 2);

        sut.remove("key1");
        assert_eq!(sut.len(), 1);

        sut.clear();
        assert_eq!(sut.len(), 0);
    }

    #[test]
    fn is_empty_returns_correct_status() {
        let mut sut = AList::new();
        assert!(sut.is_empty(), "Expected AList to be empty initially");

        sut.insert("key1", 1);
        assert!(
            !sut.is_empty(),
            "Expected AList to be non-empty after insertion"
        );

        sut.clear();
        assert!(sut.is_empty(), "Expected AList to be empty after clearing");
    }

    #[test]
    fn is_empty_after_remove() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.remove("key1");

        assert!(
            sut.is_empty(),
            "Expected AList to be empty after removal of last element"
        );
    }

    #[test]
    fn keys_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let keys: Vec<_> = sut.keys().collect();
        assert_eq!(
            &keys[..],
            &[&"key1", &"key2"],
            "Expected keys to be in the same order as they were inserted"
        );
    }

    #[test]
    fn keys_is_empty_when_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let keys: Vec<_> = sut.keys().collect();
        assert!(
            keys.is_empty(),
            "Expected keys iterator to be empty when AList is empty"
        );
    }

    #[test]
    fn keys_does_not_modify_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let mut keys = sut.keys();
        assert_eq!(keys.next(), Some(&"key1"));
        assert_eq!(keys.next(), Some(&"key2"));

        // Ensure that the original list is unchanged
        assert_eq!(sut.len(), 2);
        assert_eq!(sut.get("key1"), Some(&1));
        assert_eq!(sut.get("key2"), Some(&2));
    }

    #[test]
    fn into_keys_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let keys: Vec<_> = sut.into_keys().collect();
        assert_eq!(
            keys,
            vec!["key1", "key2"],
            "Expected keys to be in the same order as they were inserted"
        );
    }

    #[test]
    fn into_keys_consumes_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let keys: Vec<_> = sut.into_keys().collect();
        assert_eq!(keys, vec!["key1", "key2"]);
    }

    #[test]
    fn into_keys_returns_empty_when_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let keys: Vec<_> = sut.into_keys().collect();
        assert!(
            keys.is_empty(),
            "Expected into_keys to return an empty iterator when AList is empty"
        );
    }

    #[test]
    fn values_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let values: Vec<_> = sut.values().collect();
        assert_eq!(
            values,
            vec![&1, &2],
            "Expected values to be in the same order as they were inserted"
        );
    }

    #[test]
    fn values_is_empty_when_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let values: Vec<_> = sut.values().collect();
        assert!(
            values.is_empty(),
            "Expected values iterator to be empty when AList is empty"
        );
    }

    #[test]
    fn values_does_not_modify_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let mut values = sut.values();
        assert_eq!(values.next(), Some(&1));
        assert_eq!(values.next(), Some(&2));

        // Ensure that the original list is unchanged
        assert_eq!(sut.len(), 2);
        assert_eq!(sut.get("key1"), Some(&1));
        assert_eq!(sut.get("key2"), Some(&2));
    }

    #[test]
    fn values_mut_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let values: Vec<_> = sut.values_mut().collect();
        assert_eq!(
            values,
            vec![&mut 1, &mut 2],
            "Expected values to be in the same order as they were inserted"
        );
    }

    #[test]
    fn values_mut_allows_modifying_values() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        for value in sut.values_mut() {
            *value *= 2; // Doubling each value
        }

        let values: Vec<_> = sut.values().collect();
        assert_eq!(
            &values[..],
            &[&2, &4],
            "Expected values to be doubled after modification"
        );
    }

    #[test]
    fn values_mut_is_empty_when_list_is_empty() {
        let mut sut: AList<&str, i32> = AList::new();
        let values: Vec<_> = sut.values_mut().collect();
        assert!(
            values.is_empty(),
            "Expected values_mut iterator to be empty when AList is empty"
        );
    }

    #[test]
    fn values_mut_does_not_modify_the_structure_of_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Modifying values using values_mut
        for value in sut.values_mut() {
            *value *= 2;
        }

        // Ensure that the structure (keys) is unchanged
        assert_eq!(sut.len(), 2);
        assert_eq!(sut.get("key1"), Some(&2));
        assert_eq!(sut.get("key2"), Some(&4));
    }

    #[test]
    fn into_values_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let values: Vec<_> = sut.into_values().collect();
        assert_eq!(
            values,
            vec![1, 2],
            "Expected values to be in the same order as they were inserted"
        );
    }

    #[test]
    fn into_values_consumes_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let values: Vec<_> = sut.into_values().collect();
        assert_eq!(values, vec![1, 2]);
    }

    #[test]
    fn into_values_returns_empty_when_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let values: Vec<_> = sut.into_values().collect();
        assert!(
            values.is_empty(),
            "Expected into_values to return an empty iterator when AList is empty"
        );
    }

    #[test]
    fn iter_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let pairs: Vec<_> = sut.iter().collect();
        assert_eq!(
            pairs,
            vec![(&"key1", &1), (&"key2", &2)],
            "Expected key-value pairs to be in the same order as they were inserted"
        );
    }

    #[test]
    fn iter_is_empty_when_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let pairs: Vec<_> = sut.iter().collect();
        assert!(
            pairs.is_empty(),
            "Expected iter to return an empty iterator when AList is empty"
        );
    }

    #[test]
    fn iter_does_not_modify_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Iterating over the list should not modify it
        for (_key, value) in sut.iter() {
            // Just checking that we can access the values without modifying them
            assert!(*value == 1 || *value == 2);
        }

        // Ensure that the structure (key-value pairs) is unchanged
        assert_eq!(sut.len(), 2);
        assert_eq!(sut.get("key1"), Some(&1));
        assert_eq!(sut.get("key2"), Some(&2));
    }

    #[test]
    fn iter_mut_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let pairs: Vec<_> = sut.iter_mut().collect();
        assert_eq!(
            pairs,
            vec![(&"key1", &mut 1), (&"key2", &mut 2)],
            "Expected key-value pairs to be in the same order as they were inserted"
        );
    }

    #[test]
    fn iter_mut_allows_modifying_values() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        for (_key, value) in sut.iter_mut() {
            *value *= 2; // Doubling each value
        }

        let values: Vec<_> = sut.values().collect();
        assert_eq!(
            &values[..],
            &[&2, &4],
            "Expected values to be doubled after modification"
        );
    }

    #[test]
    fn iter_mut_is_empty_when_list_is_empty() {
        let mut sut: AList<&str, i32> = AList::new();
        let pairs: Vec<_> = sut.iter_mut().collect();
        assert!(
            pairs.is_empty(),
            "Expected iter_mut to return an empty iterator when AList is empty"
        );
    }

    #[test]
    fn iter_mut_does_not_modify_the_structure_of_the_list() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        // Modifying values using iter_mut
        for (_key, value) in sut.iter_mut() {
            *value *= 2;
        }

        // Ensure that the structure (keys) is unchanged
        assert_eq!(sut.len(), 2);
        assert_eq!(sut.get("key1"), Some(&2));
        assert_eq!(sut.get("key2"), Some(&4));
    }

    #[test]
    fn into_iter_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let pairs: Vec<_> = sut.into_iter().collect();
        assert_eq!(
            pairs,
            vec![("key1", 1), ("key2", 2)],
            "Expected key-value pairs to be in the same order as they were inserted"
        );
    }

    #[test]
    fn into_iter_is_empty_when_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let pairs: Vec<_> = sut.into_iter().collect();
        assert!(
            pairs.is_empty(),
            "Expected into_iter to return an empty iterator when AList is empty"
        );
    }

    #[test]
    fn into_iter_for_alist_ref_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let pairs: Vec<_> = (&sut).into_iter().collect();
        assert_eq!(
            &pairs[..],
            &[(&"key1", &1), (&"key2", &2)],
            "Expected key-value pairs to be in the same order as they were inserted"
        );
    }

    #[test]
    fn into_iter_for_alist_mut_ref_returns_correct_order_of_insertions() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let pairs: Vec<_> = (&mut sut).into_iter().collect();
        assert_eq!(
            &pairs[..],
            &[(&"key1", &mut 1), (&"key2", &mut 2)],
            "Expected key-value pairs to be in the same order as they were inserted"
        );
    }

    #[test]
    fn clone_creates_an_exact_copy() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        sut.insert("key2", 2);

        let clone = sut.clone();

        // Ensure the clone contains the same elements in the same order
        assert_eq!(sut.len(), clone.len());
        assert_eq!(sut.get("key1"), clone.get("key1"));
        assert_eq!(sut.get("key2"), clone.get("key2"));

        // Ensure the original and the clone are independent
        sut.insert("key3", 3);
        assert!(
            clone.get("key3").is_none(),
            "Expected clone to not reflect changes made to the original after cloning"
        );
    }

    #[test]
    fn clone_of_empty_list_is_empty() {
        let sut: AList<&str, i32> = AList::new();
        let clone = sut.clone();

        // Ensure the clone is also empty
        assert!(
            clone.is_empty(),
            "Expected the clone of an empty AList to also be empty"
        );
    }

    #[test]
    fn equal_lists_are_detected() {
        let mut sut1 = AList::new();
        sut1.insert("key1", 1);
        sut1.insert("key2", 2);

        let mut sut2 = AList::new();
        sut2.insert("key1", 1);
        sut2.insert("key2", 2);

        assert_eq!(sut1, sut2, "Expected two identical ALists to be equal");
    }

    #[test]
    fn equal_lists_with_different_order_are_detected() {
        let mut sut1 = AList::new();
        sut1.insert("key1", 1);
        sut1.insert("key2", 2);

        let mut sut2 = AList::new();
        sut2.insert("key2", 2);
        sut2.insert("key1", 1);

        assert_eq!(
            sut1, sut2,
            "Expected two ALists with identical keys/values but different orders to be equal"
        );
    }

    #[test]
    fn unequal_lists_are_detected_due_to_different_keys() {
        let mut sut1 = AList::new();
        sut1.insert("key1", 1);
        sut1.insert("key2", 2);

        let mut sut2 = AList::new();
        sut2.insert("key3", 1);
        sut2.insert("key2", 2);

        assert_ne!(
            sut1, sut2,
            "Expected two ALists with different keys to not be equal"
        );
    }

    #[test]
    fn unequal_lists_are_detected_due_to_different_values() {
        let mut sut1 = AList::new();
        sut1.insert("key1", 1);
        sut1.insert("key2", 2);

        let mut sut2 = AList::new();
        sut2.insert("key1", 1);
        sut2.insert("key2", 3);

        assert_ne!(
            sut1, sut2,
            "Expected two ALists with the same keys but different values to not be equal"
        );
    }

    #[test]
    fn unequal_lists_are_detected_due_to_different_lengths() {
        let mut sut1 = AList::new();
        sut1.insert("key1", 1);

        let mut sut2 = AList::new();
        sut2.insert("key1", 1);
        sut2.insert("key2", 2);

        assert_ne!(
            sut1, sut2,
            "Expected two ALists with different lengths to not be equal"
        );
    }

    #[test]
    fn debug_format_displays_empty_list() {
        let sut: AList<&str, i32> = AList::new();
        let debug_output = format!("{:?}", sut);

        assert_eq!(
            debug_output, "{}",
            "Expected debug output to show an empty AList"
        );
    }

    #[test]
    fn debug_format_displays_single_item() {
        let mut sut = AList::new();
        sut.insert("key1", 1);
        let debug_output = format!("{:?}", sut);

        assert_eq!(
            debug_output, r#"{"key1": 1}"#,
            "Expected debug output to show a single key-value pair"
        );
    }

    #[test]
    fn debug_format_preserves_order_of_insertion() {
        let mut sut = AList::new();
        sut.insert("key2", 2);
        sut.insert("key1", 1);
        let debug_output = format!("{:?}", sut);

        assert_eq!(
            debug_output, r#"{"key2": 2, "key1": 1}"#,
            "Expected debug output to preserve insertion order"
        );
    }
}
