//! Types for maintaining stores of data used during the compilation process:
//! source objects, types, symbol tables, and so on. These are roughly sets
//! for tracking data across compile phases and between IRs.

use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::num::NonZeroU32;

/// A trait automatically implemented by index types
pub trait Index: From<NonZeroU32> + Default + Clone + Eq + Hash {}

/// A macro for building implementers of Index. This is exactly analogous to
/// rustc's `rustc_index::newtype_index`.
#[macro_export]
macro_rules! store_triple {
    ($store:ident : $index:ident => $V:ty) => {
        #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
        pub struct $index(std::num::NonZeroU32);

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

        impl From<std::num::NonZeroU32> for $index {
            fn from(val: std::num::NonZeroU32) -> Self {
                Self(val)
            }
        }

        impl crate::store::Index for $index {}

        pub type $store = crate::store::Store<$index, $V>;
    };
}

/// Something like a set, which however returns indices into its backing store.
/// This makes it possible to keep references to objects that would otherwise be
/// difficult to access due to ownership contraints, and involve a lot more
/// `Rc<RefCell<T>>`s than anyone wants to deal with. It can also be used to
/// intern things, and to perform inexpensive comparisons.
#[derive(Debug)]
pub struct Store<Idx, V>
where
    Idx: Index,
{
    next_internal: std::num::NonZeroU32,
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

    fn next_idx(&mut self) -> Idx {
        let idx = self.next_internal;
        self.next_internal;
        idx.into()
    }

    pub fn insert(&mut self, val: V) -> Idx {
        let idx = self.next_idx();
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
            next_internal: NonZeroU32::new(1).unwrap(),
            backing_store: HashMap::default(),
            phantom: PhantomData,
        }
    }
}
