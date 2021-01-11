//! Types for maintaining stores of data used during the compilation process:
//! source objects, types, symbol tables, and so on. These are roughly sets
//! for tracking data across compile phases and between IRs.
//!
//! There are two main data structures in this module: the first is `Store<Idx,
//! V>`, into which you can insert values of type `V` and get `Idx` keys back to
//! retrieve them. The second is `Interner<V, Idx>`, which is a wrapper around a
//! `HashMap<V, Idx>`.

use std::collections::{
    hash_map::{Entry, Iter},
    HashMap,
};
use std::hash::Hash;
use std::marker::PhantomData;
use std::{borrow::Borrow, num::NonZeroU32};

/// The concrete index type
pub type InnerIndex = NonZeroU32;

/// A counter of `NonZeroU32`s
#[derive(Debug, Default)]
struct IdxCounter<Idx> {
    next_inner: u32,
    phantom: PhantomData<Idx>,
}

impl<Idx: Index> IdxCounter<Idx> {
    fn new() -> Self {
        IdxCounter {
            // Starts at 0, but we increment it before attempting to build a
            // nonzero value. This makes it possible to derive Default and get
            // the correct behavior.
            next_inner: 0,
            phantom: PhantomData,
        }
    }
}

impl<Idx: Index> Iterator for IdxCounter<Idx>
where
    Idx: Index,
{
    type Item = Idx;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_inner += 1;
        InnerIndex::new(self.next_inner).map(|idx| idx.into())
    }
}

/// A trait automatically implemented by index types
pub trait Index: From<InnerIndex> + Default + Clone + Eq + Hash {}

/// A macro for building implementers of Index. This is exactly analogous to
/// rustc's `rustc_index::newtype_index`. If the arrow goes left-to-right, it
/// will build a *store*, while if it goes right-to-left, it will build an *interner*.
#[macro_export]
macro_rules! index_triple {
    // This branch just makes the index type itself
    ($index:ident) => {
        #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
        pub struct $index(crate::store::InnerIndex);

        // Thm: this index has no memory overhead over a simple u32, even when
        // wrapped in an Option.
        const _: fn() = || {
            let _ = core::mem::transmute::<Option<$index>, u32>;
        };

        /// Seems to be required by some other part of my code
        impl Default for $index {
            fn default() -> Self {
                Self(std::num::NonZeroU32::new(1).unwrap())
            }
        }

        impl From<crate::store::InnerIndex> for $index {
            fn from(val: crate::store::InnerIndex) -> Self {
                Self(val)
            }
        }

        impl crate::store::Index for $index {}
    };

    // This branch is for making a store
    ($store:ident : $index:ident -> $V:ty) => {
        index_triple! { $index }
        pub type $store = crate::store::Store<$index, $V>;
    };

    // This branch is for making an interner
    ($store:ident : $index:ident <- $V:ty) => {
        index_triple! { $index }
        pub type $store = crate::store::Interner<$V, $index>;
    };
}

/// A macro for building index types together with an interner for them
#[macro_export]
macro_rules! interner_triple {
    ($store:ident : $V:ty => $index:ident) => {
        index_type! { $index }
        pub type $store = crate::store::Store<$index, $V>;
    };
}

/// Something like a set, which however returns indices into its backing store.
/// This makes it possible to keep references to objects that would otherwise be
/// difficult to access due to ownership contraints, and involve a lot more
/// `Rc<RefCell<T>>`s than anyone wants to deal with.
#[derive(Debug)]
pub struct Store<Idx, V>
where
    Idx: Index,
{
    ctr: IdxCounter<Idx>,
    backing_store: HashMap<Idx, V>,
    phantom: PhantomData<Idx>,
}

impl<Idx, V> Store<Idx, V>
where
    Idx: Index,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, val: V) -> Idx {
        // NOTE: This is *technically* a bug, but if anyone ever discovers it by
        // having more than 2^32 unique idendifiers or what-have-you, I will
        // have suffered from massive success.
        let idx = self.ctr.next().unwrap();
        self.backing_store.insert(idx.clone(), val);
        idx
    }

    pub fn get(&self, idx: &Idx) -> Option<&V> {
        self.backing_store.get(idx)
    }

    pub fn get_mut(&mut self, idx: &Idx) -> Option<&mut V> {
        self.backing_store.get_mut(idx)
    }
}

impl<Idx, V> Default for Store<Idx, V>
where
    Idx: Index,
{
    fn default() -> Self {
        Self {
            ctr: IdxCounter::new(),
            backing_store: HashMap::default(),
            phantom: PhantomData,
        }
    }
}

impl<Idx, V> std::ops::Index<Idx> for Store<Idx, V>
where
    Idx: Index,
{
    type Output = V;

    /// This can easily panic if you're not really careful about not making Inx
    /// types manually.
    fn index(&self, index: Idx) -> &Self::Output {
        self.backing_store.get(&index).unwrap()
    }
}

impl<Idx, V> std::ops::IndexMut<Idx> for Store<Idx, V>
where
    Idx: Index,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.backing_store.get_mut(&index).unwrap()
    }
}

/// The *other* main data structure in this module. This is used for
/// "insert-only" use, where you want to check membership and easily compare the
/// lightweight tokens you get back.
///
/// This just a wrapper around a hash table.
#[derive(Debug, Default)]
pub struct Interner<V, Idx> {
    ctr: IdxCounter<Idx>,
    backing_store: HashMap<V, Idx>,
}

impl<V, Idx> Interner<V, Idx>
where
    Idx: Index,
    V: Eq + Hash,
{
    fn new() -> Self {
        Self {
            ctr: IdxCounter::new(),
            backing_store: HashMap::new(),
        }
    }

    /// Insert a value in the interner, and return its index, wrapped to
    /// indicated whether this was the first insertion or some later one.
    pub fn intern(&mut self, val: V) -> Interned<Idx> {
        match self.backing_store.entry(val) {
            Entry::Occupied(entry) => Interned::Already(entry.get().clone()),
            Entry::Vacant(entry) => {
                // NOTE: Also *technically* a bug
                let idx = self.ctr.next().unwrap();
                entry.insert(idx.clone());
                Interned::First(idx)
            }
        }
    }

    pub fn get<Q: ?Sized>(&self, val: &Q) -> Option<&Idx>
    where
        V: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.backing_store.get(val)
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
