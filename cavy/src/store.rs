//! Types for maintaining stores of data used during the compilation process:
//! source objects, types, symbol tables, and so on. These are roughly sets
//! for tracking data across compile phases and between IRs.

use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;

/// This trait is applied to types that can be used to index into a Store. It
/// ultimately just wraps a usize, but should do so opaquely.
///
/// As I somehow keep converging on the same design choices as rustc, it might
/// be worth pointing out that this is exactly analogous to `rustc_index::Idx`.
pub trait Index<V>: From<u32> + Eq + Hash + Copy {}

/// A macro for building implementers of Index. This is exactly analogous to
/// rustc's `rustc_index::newtype_index`.
#[macro_export]
macro_rules! store_triple {
    ($store:ident : $index:ident => $V:ty) => {
        #[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Default)]
        pub struct $index(u32);

        impl From<u32> for $index {
            fn from(val: u32) -> Self {
                Self(val)
            }
        }

        impl crate::store::Index<$V> for $index {}

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
    Idx: Index<V>,
{
    next_internal: u32,
    backing_store: HashMap<Idx, V>,
    phantom: PhantomData<Idx>,
}

impl<Idx, V> Store<Idx, V>
where
    Idx: Index<V>,
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
        self.backing_store.insert(idx, val);
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
    Idx: Index<V>,
{
    fn default() -> Self {
        Self {
            // Start at 1 because you might later want to make this non-nullable
            next_internal: 1,
            backing_store: HashMap::new(),
            phantom: PhantomData,
        }
    }
}
