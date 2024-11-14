use core::borrow::Borrow;
use core::fmt;
use core::marker::PhantomData;

use crate::AList;

pub struct Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    key: &'q Q,
    pub(super) position: usize,
    phantom: PhantomData<*mut AList<K, V>>,
}

impl<'q, Q, K, V> From<&'q Q> for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn from(key: &'q Q) -> Self {
        Self::new(key)
    }
}

impl<'q, Q, K, V> Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    pub(super) const fn new_with_position(key: &'q Q, position: usize) -> Self {
        Self {
            key,
            position,
            phantom: PhantomData,
        }
    }

    pub const fn new(key: &'q Q) -> Self {
        Self::new_with_position(key, usize::MAX)
    }

    pub fn key(&self) -> &Q {
        self.key
    }
}

impl<'q, Q, K, V> PartialEq for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl<'q, Q, K, V> fmt::Debug for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: fmt::Debug + Eq + ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bookmark")
            .field("key", &self.key())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use crate::Bookmark;

    #[test]
    fn bookmark_from_and_new_give_the_same_instances() {
        assert_eq!(Bookmark::from("key"), Bookmark::<_, &str, i32>::new("key"));
    }

    #[test]
    fn bookmark_debug_format() {
        let sut = Bookmark::<_, &str, i32>::new("key1");
        let debug_output = format!("{:?}", sut);

        assert_eq!(debug_output, r#"Bookmark { key: "key1", .. }"#,);
    }
}
