//! Types for maintaining stores of data used during the compilation process:
//! source objects, types, symbol tables, and so on. These are roughly sets
//! for tracking data across compile phases and between IRs.
//!
//! There are two main data structures in this module: the first is `Store<Idx,
//! V>`, into which you can insert values of type `V` and get `Idx` keys back to
//! retrieve them. The second is `Interner<V, Idx>`, which is a wrapper around a
//! `HashMap<V, Idx>`.

use bitvec::prelude::*;
use std::marker::PhantomData;
use std::{borrow::Borrow, hash::Hash, rc::Rc};
use std::{
    collections::{
        hash_map::{Entry, Iter},
        HashMap,
    },
    iter::FromIterator,
};

use crate::util::FmtWith;

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
}

impl<I: Index> Iterator for Counter<I> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        let next = From::<u32>::from(self.inner);
        self.inner += 1;
        Some(next)
    }
}

// NOTE: Not actually using this yet, but it should be useful.
/// A set of indices backed by a `BitVec`
#[derive(Clone, PartialEq, Eq)]
pub struct BitSet<I: Index> {
    data: BitVec,
    _d: PhantomData<I>,
}

impl<I: Index> BitSet<I> {
    pub fn full(n: usize) -> Self {
        Self {
            data: bitvec![1; n],
            _d: PhantomData,
        }
    }

    pub fn empty(n: usize) -> Self {
        Self {
            data: bitvec![0; n],
            _d: PhantomData,
        }
    }

    pub fn contains(&self, idx: &I) -> bool {
        let u: u32 = (*idx).into();
        let us = u as usize;
        self.data[us]
    }

    pub fn iter(&self) -> impl '_ + Iterator<Item = I> {
        self.data.iter().enumerate().filter_map(|(idx, bit)| {
            if *bit {
                Some(I::from(idx as u32))
            } else {
                None
            }
        })
    }

    pub fn get_mut(&mut self, idx: I) -> Option<BitRef<'_, bitvec::ptr::Mut>> {
        self.data.get_mut(idx.into() as usize)
    }

    pub fn as_mut_bitslice(&mut self) -> &mut BitSlice {
        self.data.as_mut_bitslice()
    }

    /// FIXME: should really have "insert, remove"
    pub fn set(&mut self, idx: I, val: bool) {
        *self.get_mut(idx).unwrap() = val;
    }
}

impl<I: Index> From<BitVec> for BitSet<I> {
    fn from(bits: BitVec) -> Self {
        Self {
            data: bits,
            _d: PhantomData,
        }
    }
}

impl<I: Index> std::fmt::Display for BitSet<I>
where
    I: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut elems = self.iter();
        f.write_str("{")?;
        if let Some(head) = elems.next() {
            write!(f, "{}", head)?;
            for elem in elems {
                write!(f, ", {}", elem)?;
            }
        }
        f.write_str("}")
    }
}

impl<I: Index, F> FmtWith<F> for BitSet<I>
where
    I: FmtWith<F>,
{
    fn fmt(&self, data: &F, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut elems = self.iter();
        f.write_str("{")?;
        if let Some(head) = elems.next() {
            write!(f, "{}", head.fmt_with(data))?;
            for elem in elems {
                write!(f, ", {}", elem.fmt_with(data))?;
            }
        }
        f.write_str("}")
    }
}

impl<I: Index> std::ops::BitOr for BitSet<I> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            data: self.data | rhs.data,
            _d: PhantomData,
        }
    }
}

impl<I: Index> std::ops::BitAnd for BitSet<I> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            data: self.data & rhs.data,
            _d: PhantomData,
        }
    }
}

/// Create a newtyped bitset that implements all the right things
#[macro_export]
macro_rules! bitset {
    ($name:ident($I:ty)) => {
        #[derive(Clone, PartialEq, Eq)]
        pub struct $name($crate::store::BitSet<$I>);

        impl $name {
            pub fn full(n: usize) -> Self {
                Self(BitSet::<$I>::full(n))
            }

            pub fn empty(n: usize) -> Self {
                Self(BitSet::<$I>::empty(n))
            }

            pub fn contains(&self, idx: &$I) -> bool {
                self.0.contains(idx)
            }

            pub fn iter(&self) -> impl '_ + Iterator<Item = $I> {
                self.0.iter()
            }

            pub fn get_mut(&mut self, idx: $I) -> Option<BitRef<'_, bitvec::ptr::Mut>> {
                self.0.get_mut(idx)
            }

            pub fn set(&mut self, idx: $I, val: bool) {
                self.0.set(idx, val)
            }
        }

        // Yeah, use the inner Debug for the outer Display for now.
        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl std::ops::BitOr for $name {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output {
                Self(self.0 | rhs.0)
            }
        }

        impl std::ops::BitAnd for $name {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self::Output {
                Self(self.0 & rhs.0)
            }
        }
    };
}

/// A trait automatically implemented by index types
///
/// TODO I have to rename this; it conflicts with `std::ops::Index`
pub trait Index: Default + Clone + Copy + Eq + From<u32> + Into<u32> {}

/// A macro for building implementers of Index. This is exactly analogous to
/// rustc's `rustc_index::newtype_index`.
///
/// Note: don't remove `Copy` from the index types. This isn't just handy; it
/// actually improves performance. `clear`ing a HashMap takes O(1) time for
/// `Copy` types, while it takes O(n) time for non-`Copy` types.
#[macro_export]
macro_rules! index_type {
    ($index:ident) => {
        #[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $index(u32);

        impl $crate::store::Index for $index {}

        impl ::std::fmt::Debug for $index {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        /// Seems to be required by some other part of my code
        impl Default for $index {
            fn default() -> Self {
                Self(0)
            }
        }

        impl From<u32> for $index {
            fn from(n: u32) -> Self {
                Self(n)
            }
        }

        impl From<$index> for u32 {
            fn from(idx: $index) -> u32 {
                idx.0
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

#[derive(Debug, PartialEq, Eq, Clone)]
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

    pub fn len(&self) -> usize {
        self.backing_store.len()
    }

    pub fn is_empty(&self) -> bool {
        self.backing_store.is_empty()
    }

    pub fn insert(&mut self, item: V) -> Idx {
        let idx = Idx::from(self.len() as u32);
        self.backing_store.push(item);
        idx
    }

    pub fn iter(&self) -> std::slice::Iter<'_, V> {
        self.backing_store.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, V> {
        self.backing_store.iter_mut()
    }

    pub fn into_iter(self) -> std::vec::IntoIter<V> {
        self.backing_store.into_iter()
    }

    pub fn extend<It>(&mut self, iter: It)
    where
        It: Iterator<Item = V>,
    {
        self.backing_store.extend(iter)
    }

    // Safety: `idx` out of bounds is undefined behavior
    pub unsafe fn get_unchecked_mut(&mut self, idx: Idx) -> &mut V {
        self.backing_store.get_unchecked_mut(idx.into() as usize)
    }

    // Safety: `idx` out of bounds is undefined behavior; `fst` and `snd` must
    // not be equal.
    pub unsafe fn get_two_unchecked_mut(&mut self, fst: Idx, snd: Idx) -> (&mut V, &mut V) {
        let fst = &mut *(self.get_unchecked_mut(fst) as *mut _);
        let snd = &mut *(self.get_unchecked_mut(snd) as *mut _);
        (fst, snd)
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
            let idx = Idx::from(idx as u32);
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
        &self.backing_store[index.into() as usize]
    }
}

impl<Idx: Index, V> std::ops::IndexMut<Idx> for Store<Idx, V> {
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.backing_store[index.into() as usize]
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
