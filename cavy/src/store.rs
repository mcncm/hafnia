//! Types for maintaining stores of data used during the compilation process:
//! source objects, types, symbol tables, and so on. These are roughly sets
//! for tracking data across compile phases and between IRs.
//!
//! There are two main data structures in this module: the first is `Store<Idx,
//! V>`, into which you can insert values of type `V` and get `Idx` keys back to
//! retrieve them. The second is `Interner<V, Idx>`, which is a wrapper around a
//! `HashMap<V, Idx>`.

use serde::{Deserialize, Serialize};
use std::collections::{
    hash_map::{Entry, Iter},
    HashMap,
};
use std::marker::PhantomData;
use std::{borrow::Borrow, hash::Hash, rc::Rc};

/// A trait automatically implemented by index types
pub trait Index: Default + Clone + Copy + Eq {
    fn new(u: u32) -> Self;
    fn into_usize(&self) -> usize;
}

/// A macro for building implementers of Index. This is exactly analogous to
/// rustc's `rustc_index::newtype_index`.
///
/// Note: don't remove `Copy` from the index types. This isn't just handy; it
/// actually improves performance. `clear`ing a HashMap takes O(1) time for
/// `Copy` types, while it takes O(n) time for non-`Copy` types.
#[macro_export]
macro_rules! index_type {
    ($index:ident) => {
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
        pub struct $index(u32);

        /// Seems to be required by some other part of my code
        impl Default for $index {
            fn default() -> Self {
                Self(0)
            }
        }

        impl crate::store::Index for $index {
            fn new(u: u32) -> Self {
                Self(u)
            }

            fn into_usize(&self) -> usize {
                self.0 as usize
            }
        }
    };
}

#[macro_export]
macro_rules! store_type {
    // This branch just makes the index type itself

    // This branch is for making a store
    ($store:ident : $index:ident -> $V:ty) => {
        crate::index_type! { $index }
        pub type $store = crate::store::Store<$index, $V>;
    };
}

#[macro_export]
macro_rules! interner_type {
    ($interner:ident : $index:ident -> $V:ty) => {
        crate::index_type! { $index }
        pub type $interner = crate::store::Interner<$index, $V>;
    };
}

#[derive(Debug)]
pub struct Store<Idx, V> {
    backing_store: Vec<V>,
    phantom: PhantomData<Idx>,
}

impl<Idx, V> Store<Idx, V>
where
    Idx: Index,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(n: usize) -> Self {
        Self {
            backing_store: Vec::with_capacity(n),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.backing_store.len()
    }

    pub fn insert(&mut self, item: V) -> Idx {
        let idx = Idx::new(self.len() as u32);
        self.backing_store.push(item);
        idx
    }

    pub fn iter(&self) -> std::slice::Iter<'_, V> {
        self.backing_store.iter()
    }
}

impl<Idx, V> Default for Store<Idx, V> {
    fn default() -> Self {
        Self {
            backing_store: vec![],
            phantom: PhantomData,
        }
    }
}

impl<Idx, V> std::ops::Index<Idx> for Store<Idx, V>
where
    Idx: Index,
{
    type Output = V;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.backing_store[index.into_usize()]
    }
}

impl<Idx, V> std::ops::IndexMut<Idx> for Store<Idx, V>
where
    Idx: Index,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.backing_store[index.into_usize()]
    }
}

/// Whether an interned value was the first to be inserted or a subsequent
/// insertion.
#[derive(Debug)]
pub enum Interned<Idx> {
    Already(Idx),
    First(Idx),
}

impl<Idx> Interned<Idx> {
    /// Return the inner value. Maybe it shouldn't be called this, as it can't
    /// panic.
    pub fn unwrap(self) -> Idx {
        match self {
            Self::Already(idx) => idx,
            Self::First(idx) => idx,
        }
    }
}

/// The *other* main data structure, which is like an invertible finite map.
#[derive(Debug, Default)]
pub struct Interner<Idx, V>
where
    Idx: Index,
    V: Eq + Hash,
{
    /// Let us defer the awkward lifetime issues for now by cloning all of the
    /// stored items. This *explicitly* throws away performance, but it's a lot
    /// easier.
    store: Store<Idx, V>,
    reverse: HashMap<V, Idx>,
}

impl<Idx, V> Interner<Idx, V>
where
    Idx: Index,
    V: Eq + Hash + Clone,
{
    pub fn new() -> Self {
        Self {
            store: Store::new(),
            reverse: HashMap::new(),
        }
    }

    pub fn intern(&mut self, item: V) -> Idx {
        if let Some(&item) = self.reverse.get(&item) {
            return item;
        }

        let idx = self.store.insert(item.clone());
        self.reverse.insert(item, idx);
        idx
    }

    pub fn contains<Q: ?Sized>(&self, item: &Q) -> bool
    where
        V: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.reverse.contains_key(item)
    }
}

impl<Idx, V> std::ops::Index<Idx> for Interner<Idx, V>
where
    Idx: Index,
    V: Eq + Hash,
{
    type Output = V;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.store[index]
    }
}

impl<Idx, V> std::ops::IndexMut<Idx> for Interner<Idx, V>
where
    Idx: Index,
    V: Eq + Hash,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.store[index]
    }
}
