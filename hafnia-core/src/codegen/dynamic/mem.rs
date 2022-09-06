use std::ops::{self, Deref};

use crate::{
    circuit::{Cbit, FreeState, Inst, Qbit},
    store::Counter,
    types::{Offset, TyId, TypeSize},
};

use super::*;

pub trait MemFree<T> {
    fn free<S>(&mut self, items: S, state: FreeState)
    where
        S: Iterator<Item = T>;
}

trait Allocator<T>: Iterator<Item = T> + MemFree<T> {}

struct ThreeWayAllocator<T, I: Iterator<Item = T>> {
    /// Unused items
    fresh: I,
    // `Vec` probably better for locality?
    /// A clean free set that can be reallocated immediately
    clean: VecDeque<T>,
    /// A dirty free set that can be scheduled for reset
    dirty: VecDeque<T>,
}

impl<T, I: Iterator<Item = T>> ThreeWayAllocator<T, I> {
    fn new(items: I) -> Self {
        Self {
            fresh: items,
            clean: VecDeque::new(),
            dirty: VecDeque::new(),
        }
    }
}

impl<T, I: Iterator<Item = T>> Iterator for ThreeWayAllocator<T, I> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let bit = self.clean.pop_front().or_else(|| self.fresh.next());
        bit
    }
}

impl<T, I: Iterator<Item = T>> MemFree<T> for ThreeWayAllocator<T, I> {
    fn free<S>(&mut self, items: S, state: FreeState)
    where
        S: Iterator<Item = T>,
    {
        match state {
            FreeState::Clean => self.clean.extend(items),
            FreeState::Dirty => self.dirty.extend(items),
        }
    }
}

impl<T, I: Iterator<Item = T>> Allocator<T> for ThreeWayAllocator<T, I> {}

type QbAlloc = ThreeWayAllocator<Qbit, Counter<Qbit>>;
type CbAlloc = ThreeWayAllocator<Cbit, Counter<Cbit>>;

pub struct BitAllocators {
    class: CbAlloc,
    quant: QbAlloc,
}

impl BitAllocators {
    pub fn new() -> Self {
        Self {
            quant: QbAlloc::new(Counter::new()),
            class: CbAlloc::new(Counter::new()),
        }
    }

    pub fn alloc_for_ty(&mut self, ty: TyId, ctx: &Context) -> BitArray {
        let sz = ty.size(&ctx);
        BitArray {
            cbits: self.class.by_ref().take(sz.csize).collect(),
            qbits: self.quant.by_ref().take(sz.qsize).collect(),
        }
    }
}

impl<'a, 'c> MemFree<Qbit> for CircAssembler<'a, 'c> {
    fn free<S>(&mut self, items: S, state: FreeState)
    where
        S: Iterator<Item = Qbit>,
    {
        self.allocators.quant.free(items, state);
    }
}

impl<'a, 'c> MemFree<Cbit> for CircAssembler<'a, 'c> {
    fn free<S>(&mut self, items: S, state: FreeState)
    where
        S: Iterator<Item = Cbit>,
    {
        self.allocators.class.free(items, state);
    }
}

impl<'a> InterpreterState<'a> {
    pub fn bitset_ranges(&self, place: &Place) -> (ops::Range<usize>, ops::Range<usize>) {
        // start with the root type
        let ty = self.locals[place.root].ty;

        // traverse the allocation
        let (ty, start) = place
            .path
            .iter()
            .fold((ty, Offset::zero()), |(ty, offset), proj| {
                let (newty, delta) = ty.slot(proj, self.ctx);
                (newty, offset + delta)
            });
        let sz = *ty.size(self.ctx);
        let end = start + sz;
        (start.quant..end.quant, start.class..end.class)
    }

    /// Get a sub-allocation at a place.
    pub fn bits_at(&self, place: &Place) -> BitSlice {
        let ranges = self.bitset_ranges(place);
        self.bindings[place.root].index(ranges)
    }

    /// Initialize the locals addresses: copy parameter addresses and allocate
    /// fresh bits for the rest of them, from the *global allocator*.
    pub fn mem_init<'b, I>(
        &mut self,
        mut params: I,
        allocator: &mut BitAllocators,
        // NOTE: 2021-05-18 this parameter is a *hack* to get around ugly
        // circuits.
        shared_mem: &HashMap<LocalId, Place>,
    ) where
        I: Iterator<Item = BitSlice<'b>>,
    {
        let mut locals = self.locals.idx_enumerate();
        // First copy in the parameter addresses
        while let Some(param) = params.next() {
            locals.next().expect("more parameters than locals");
            self.bindings.insert(param.to_owned());
        }

        for (local_id, local) in locals {
            let ty = local.ty;

            // NOTE: this check, and this `shared_mem` thing, are bad hacks.
            // They must be replaced by *real* analyses and optimizations.
            if shared_mem.contains_key(&local_id) {
                // Just save these for later, after we know everything else has
                // been inserted.
                self.bindings.insert(BitArray::default());
            } else {
                let bits = allocator.alloc_for_ty(ty, self.ctx);
                self.bindings.insert(bits);
            }
        }
        // And then finish up the shared-memory ones.
        for (local_id, referent) in shared_mem.iter() {
            let bits = referent.as_bits(self).to_owned();
            self.bindings[*local_id] = bits;
        }

        debug_assert_eq!(self.locals.len(), self.bindings.len());
    }
}

/// An allocation of locally indexed virtual addresses.
///
/// NOTE: careful, this name conflicts with one in the `bitvec` crate.
#[derive(Debug, Clone, Default)]
pub struct BitArray {
    pub qbits: Vec<Qbit>,
    pub cbits: Vec<Cbit>,
}

impl BitArray {
    pub fn empty() -> Self {
        Self {
            qbits: Vec::new(),
            cbits: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.qbits.len() == 0 && self.cbits.len() == 0
    }

    // NOTE: this is not going to be very efficient at all, and these values
    // will soon be overwritten. We could accomplish the same thing lazily, and
    // could also use uninitialied memory.
    /// Create an uninitialized set of address bindings
    pub fn uninit(sz: &TypeSize) -> Self {
        Self {
            qbits: vec![Qbit::from(0); sz.qsize],
            cbits: vec![Cbit::from(0); sz.csize],
        }
    }

    pub fn append(&mut self, other: &mut BitArray) {
        self.qbits.append(&mut other.qbits);
        self.cbits.append(&mut other.cbits);
    }

    pub fn copy_from_slice(&mut self, slice: &BitSlice) {
        self.as_slice_mut().copy_from_slice(slice);
    }

    pub fn as_slice(&self) -> BitSlice {
        BitSlice {
            qbits: &self.qbits,
            cbits: &self.cbits,
        }
    }

    pub fn as_slice_mut(&mut self) -> BitSliceMut {
        BitSliceMut {
            qbits: &mut self.qbits,
            cbits: &mut self.cbits,
        }
    }

    // NOTE I don't think this can actually be done with the Index trait without
    // GATs.
    pub fn index<'b: 'a, 'a>(
        &'b self,
        idx: (std::ops::Range<usize>, std::ops::Range<usize>),
    ) -> BitSlice<'a> {
        BitSlice {
            qbits: &self.qbits[idx.0],
            cbits: &self.cbits[idx.1],
        }
    }

    pub fn index_mut<'b: 'a, 'a>(
        &'b mut self,
        idx: (std::ops::Range<usize>, std::ops::Range<usize>),
    ) -> BitSliceMut<'a> {
        BitSliceMut {
            qbits: &mut self.qbits[idx.0],
            cbits: &mut self.cbits[idx.1],
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct BitSlice<'a> {
    pub qbits: &'a [Qbit],
    pub cbits: &'a [Cbit],
}

impl BitSlice<'_> {
    // NOTE should really use the ToOwned trait
    pub fn to_owned(&self) -> BitArray {
        BitArray {
            qbits: self.qbits.to_owned(),
            cbits: self.cbits.to_owned(),
        }
    }
}

pub struct BitSliceMut<'a> {
    pub qbits: &'a mut [Qbit],
    pub cbits: &'a mut [Cbit],
}

impl<'a> BitSliceMut<'a> {
    fn copy_from_slice(&mut self, other: &BitSlice) {
        self.qbits.copy_from_slice(other.qbits);
        self.cbits.copy_from_slice(other.cbits);
    }
}

/// Something that can be viewed as a `BitSlice` with the help of an environment
pub trait AsBits {
    fn as_bits<'a>(&'a self, st: &'a InterpreterState) -> BitSlice<'a>;
}

impl<'a> AsBits for BitSlice<'a> {
    fn as_bits<'b>(&'b self, _st: &'b InterpreterState) -> BitSlice<'b> {
        Self {
            qbits: &self.qbits,
            cbits: &self.cbits,
        }
    }
}

impl AsBits for Place {
    fn as_bits<'a>(&'a self, st: &'a InterpreterState) -> BitSlice<'a> {
        st.bits_at(self)
    }
}

impl AsBits for LocalId {
    fn as_bits<'a>(&'a self, st: &'a InterpreterState) -> BitSlice<'a> {
        st.bits_at(&<Place>::from(*self))
    }
}

impl AsBits for BitArray {
    fn as_bits<'a>(&'a self, _st: &'a InterpreterState) -> BitSlice<'a> {
        self.as_slice()
    }
}
