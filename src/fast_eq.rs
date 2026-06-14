//! Marker trait for keys with cheap equality.
//!
//! `AList` performs linear scans for key lookup. The [`FastEq`] marker keeps
//! lookup APIs intentionally focused on key types whose equality checks are
//! expected to be trivial, such as integers, characters, and simple wrappers.
//! This is important because every lookup may compare several keys.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use core::num::NonZero;

/// Marker trait for key types with trivial equality comparisons.
///
/// `AList` uses linear scans for key lookup, so it accepts keys whose equality
/// checks are expected to be cheap. This trait is intentionally narrower than
/// `Eq`; for example, `String` does not implement `FastEq` because string
/// equality is `O(n)` in the string length.
///
/// Prefer compact keys with constant-time equality, such as integer IDs,
/// indices, characters, or interned symbols. Large keys also make each
/// `(K, V)` pair larger, which can reduce cache-line efficiency while `AList`
/// scans its contiguous storage.
pub trait FastEq: Eq {}

impl FastEq for bool {}
impl FastEq for char {}

impl FastEq for u8 {}
impl FastEq for u16 {}
impl FastEq for u32 {}
impl FastEq for u64 {}
impl FastEq for u128 {}
impl FastEq for usize {}

impl FastEq for i8 {}
impl FastEq for i16 {}
impl FastEq for i32 {}
impl FastEq for i64 {}
impl FastEq for i128 {}
impl FastEq for isize {}

impl FastEq for NonZero<u8> {}
impl FastEq for NonZero<u16> {}
impl FastEq for NonZero<u32> {}
impl FastEq for NonZero<u64> {}
impl FastEq for NonZero<u128> {}
impl FastEq for NonZero<usize> {}

impl FastEq for NonZero<i8> {}
impl FastEq for NonZero<i16> {}
impl FastEq for NonZero<i32> {}
impl FastEq for NonZero<i64> {}
impl FastEq for NonZero<i128> {}
impl FastEq for NonZero<isize> {}

impl<T: FastEq> FastEq for Option<T> {}

impl<T: FastEq + ?Sized> FastEq for Box<T> {}
impl<T: FastEq + ?Sized> FastEq for Rc<T> {}
impl<T: FastEq + ?Sized> FastEq for Arc<T> {}

impl<T: FastEq + ?Sized> FastEq for &T {}

#[cfg(test)]
mod tests {
    use alloc::{boxed::Box, rc::Rc, sync::Arc};
    use core::num::NonZero;

    use crate::FastEq;

    fn accepts_fast_eq<T: FastEq>(_: T) {}

    #[test]
    fn primitive_and_nonzero_keys_are_fast_eq() {
        accepts_fast_eq(true);
        accepts_fast_eq('a');
        accepts_fast_eq(1_u8);
        accepts_fast_eq(NonZero::<u8>::new(1).unwrap());
    }

    #[test]
    #[allow(clippy::needless_borrows_for_generic_args)]
    fn wrapper_keys_are_fast_eq_when_inner_key_is_fast_eq() {
        accepts_fast_eq(Some('a'));
        accepts_fast_eq(Box::new('a'));
        accepts_fast_eq(Rc::new('a'));
        accepts_fast_eq(Arc::new('a'));
        accepts_fast_eq(&Box::new('a'));
    }
}
