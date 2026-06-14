//! Convenience macro for constructing [`AList`](crate::AList) values.

/// Creates an [`AList`](crate::AList) from key-value pairs.
///
/// Duplicate keys keep their first insertion position and replace the existing
/// value, matching [`AList::from_iter`](crate::AList::from_iter).
///
/// # Examples
///
/// ```rust
/// use alist::alist;
///
/// let list = alist! {
///     'a' => 1,
///     'b' => 2,
///     'a' => 3,
/// };
///
/// assert_eq!(list.get(&'a'), Some(&3));
/// assert_eq!(list.get(&'b'), Some(&2));
/// ```
#[macro_export]
macro_rules! alist {
    () => {
        $crate::AList::new()
    };
    ($($k:expr => $v:expr),+ $(,)?) => {
        $crate::AList::from_iter([$(($k, $v)),+])
    };
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};

    use crate::AList;

    #[test]
    fn empty_macro_creates_empty_alist() {
        let sut: AList<char, i32> = alist! {};

        assert!(sut.is_empty());
    }

    #[test]
    fn macro_accepts_trailing_comma_and_overwrites_duplicate_keys() {
        let sut = alist! {
            'a' => 1,
            'b' => 2,
            'a' => 3,
        };

        let pairs: Vec<_> = sut.into_iter().collect();
        assert_eq!(pairs, vec![('a', 3), ('b', 2)]);
    }
}
