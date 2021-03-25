//! Types for maintaining stores of data used during the compilation process:
//! source objects, types, symbol tables, and so on. These are roughly sets
//! for tracking data across compile phases and between IRs.
//!
//! There are two main data structures in this module: the first is `Store<Idx,
//! V>`, into which you can insert values of type `V` and get `Idx` keys back to
//! retrieve them. The second is `Interner<V, Idx>`, which is a wrapper around a
//! `HashMap<V, Idx>`.

use serde::{Deserialize, Serialize};
use std::marker::PhantomData;
use std::{borrow::Borrow, hash::Hash, rc::Rc};
use std::{
    collections::{
        hash_map::{Entry, Iter},
        HashMap,
    },
    iter::FromIterator,
};

/// A trait automatically implemented by index types
pub trait Index: Default + Clone + Copy + Eq {
    fn new(u: u32) -> Self;
    fn into_usize(&self) -> usize;
}

/// An index counter, which you might want to make independently of a store or
/// interner.
#[derive(Default, Debug)]
pub struct Counter<I: Index> {
    inner: u32,
    phantom: PhantomData<I>,
}

impl<I: Index> Counter<I> {
    pub fn new() -> Self {
        Self {
            inner: 0,
            phantom: PhantomData,
        }
    }

    pub fn new_index(&mut self) -> I {
        let idx = I::new(self.inner);
        self.inner += 1;
        idx
    }

    /// The number of indices emitted so far
    pub fn count(&self) -> usize {
        self.inner as usize
    }
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
        #[derive(
            Debug,
            Clone,
            Copy,
            Hash,
            PartialEq,
            Eq,
            PartialOrd,
            Ord,
            serde::Serialize,
            serde::Deserialize,
        )]
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

impl<Idx: Index, V> Store<Idx, V> {
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

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.backing_store.is_empty()
    }

    pub fn insert(&mut self, item: V) -> Idx {
        let idx = Idx::new(self.len() as u32);
        self.backing_store.push(item);
        idx
    }

    pub fn iter(&self) -> std::slice::Iter<'_, V> {
        self.backing_store.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, V> {
        self.backing_store.iter_mut()
    }

    // This isn't really the conventional Rust API: `enumerate` is something that takes
    // an _iterator_. I _could_ define this on the thing that *iter* returns, but
    // I'd need two new iterable types.
    pub fn idx_enumerate(&self) -> StoreEnumerate<'_, Idx, V> {
        StoreEnumerate::new(self)
    }
}

pub struct StoreEnumerate<'i, Idx, V> {
    iter: std::iter::Enumerate<std::slice::Iter<'i, V>>,
    phantom: PhantomData<Idx>,
}

impl<'i, Idx: Index, V> StoreEnumerate<'i, Idx, V> {
    fn new(store: &'i Store<Idx, V>) -> Self {
        Self {
            iter: store.iter().enumerate(),
            phantom: PhantomData,
        }
    }
}

impl<'i, Idx: Index, V> Iterator for StoreEnumerate<'i, Idx, V> {
    type Item = (Idx, &'i V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(idx, v)| {
            // NOTE is this always safe?
            let idx = Idx::new(idx as u32);
            (idx, v)
        })
    }
}

impl<Idx, V> FromIterator<V> for Store<Idx, V> {
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        let backing_store = iter.into_iter().collect();
        Self {
            backing_store,
            phantom: PhantomData,
        }
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

impl<Idx: Index, V> std::ops::Index<Idx> for Store<Idx, V> {
    type Output = V;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.backing_store[index.into_usize()]
    }
}

impl<Idx: Index, V> std::ops::IndexMut<Idx> for Store<Idx, V> {
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
