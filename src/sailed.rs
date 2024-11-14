use std::borrow::Borrow;

use crate::{AList, Bookmark};

pub trait Get<K, V> {
    fn get(self, alist: &AList<K, V>) -> Option<&V>;
}

impl<'q, Q, K, V> Get<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get(self, alist: &AList<K, V>) -> Option<&V> {
        if !alist.is_valid(self) {
            self.position = alist.position(self.key())?;
        }

        let (_, v) = &alist.pairs[self.position];
        Some(v)
    }
}

impl<Q, K, V> Get<K, V> for &Q
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get(self, alist: &AList<K, V>) -> Option<&V> {
        alist.find(self).map(|(_, v)| v)
    }
}

pub trait GetMut<K, V> {
    fn get_mut(self, alist: &mut AList<K, V>) -> Option<&mut V>;
}

impl<'q, Q, K, V> GetMut<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get_mut(self, alist: &mut AList<K, V>) -> Option<&mut V> {
        if !alist.is_valid(self) {
            self.position = alist.position(self.key())?;
        }

        let (_, v) = &mut alist.pairs[self.position];
        Some(v)
    }
}

impl<Q, K, V> GetMut<K, V> for &Q
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get_mut(self, alist: &mut AList<K, V>) -> Option<&mut V> {
        alist.find_mut(self).map(|(_, v)| v)
    }
}

pub trait GetKeyValue<K, V> {
    fn get_key_value(self, alist: &AList<K, V>) -> Option<(&K, &V)>;
}

impl<'q, Q, K, V> GetKeyValue<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get_key_value(self, alist: &AList<K, V>) -> Option<(&K, &V)> {
        if !alist.is_valid(self) {
            self.position = alist.position(self.key())?;
        }

        let (k, v) = &alist.pairs[self.position];
        Some((k, v))
    }
}

impl<Q, K, V> GetKeyValue<K, V> for &Q
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get_key_value(self, alist: &AList<K, V>) -> Option<(&K, &V)> {
        alist.find(self)
    }
}

pub trait GetKeyValueMut<K, V> {
    fn get_key_value_mut(self, alist: &mut AList<K, V>) -> Option<(&K, &mut V)>;
}

impl<'q, Q, K, V> GetKeyValueMut<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get_key_value_mut(self, alist: &mut AList<K, V>) -> Option<(&K, &mut V)> {
        if !alist.is_valid(self) {
            self.position = alist.position(self.key())?;
        }

        let (k, v) = &mut alist.pairs[self.position];
        Some((&*k, v))
    }
}

impl<Q, K, V> GetKeyValueMut<K, V> for &Q
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn get_key_value_mut(self, alist: &mut AList<K, V>) -> Option<(&K, &mut V)> {
        alist.find_mut(self)
    }
}

pub trait ContainsKey<K, V> {
    fn contains_key(self, alist: &AList<K, V>) -> bool;
}

impl<'q, Q, K, V> ContainsKey<K, V> for &mut Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn contains_key(self, alist: &AList<K, V>) -> bool {
        if !alist.is_valid(self) {
            match alist.position(self.key()) {
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
    Q: Eq + ?Sized,
{
    fn contains_key(self, alist: &AList<K, V>) -> bool {
        alist.pairs.iter().any(|(k, _)| k.borrow() == self)
    }
}

pub trait Remove<K, V> {
    fn remove(self, alist: &mut AList<K, V>) -> Option<V>;
}

impl<'q, Q, K, V> Remove<K, V> for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn remove(mut self, alist: &mut AList<K, V>) -> Option<V> {
        if !alist.is_valid(&self) {
            self.position = alist.position(self.key())?;
        }

        let (_, v) = alist.pairs.swap_remove(self.position);
        Some(v)
    }
}

impl<Q, K, V> Remove<K, V> for &Q
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn remove(self, alist: &mut AList<K, V>) -> Option<V> {
        alist.position(self).map(|position| {
            let (_, v) = alist.pairs.swap_remove(position);
            v
        })
    }
}

pub trait RemoveEntry<K, V> {
    fn remove_entry(self, alist: &mut AList<K, V>) -> Option<(K, V)>;
}

impl<'q, Q, K, V> RemoveEntry<K, V> for Bookmark<'q, Q, K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn remove_entry(mut self, alist: &mut AList<K, V>) -> Option<(K, V)> {
        if !alist.is_valid(&self) {
            self.position = alist.position(self.key())?;
        }

        Some(alist.pairs.swap_remove(self.position))
    }
}

impl<Q, K, V> RemoveEntry<K, V> for &Q
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn remove_entry(self, alist: &mut AList<K, V>) -> Option<(K, V)> {
        alist
            .position(self)
            .map(|position| alist.pairs.swap_remove(position))
    }
}
