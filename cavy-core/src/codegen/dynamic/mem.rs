use std::ops;

use crate::types::{TyId, TypeSize};

use super::*;

struct Allocator<T, I>
where
    I: Iterator<Item = T>,
{
    /// Unused items
    fresh: I,
    /// A clean free set that can be reallocated immediately
    clean: Vec<T>,
    /// A dirty free set that should be scheduled for reset
    dirty: VecDeque<T>,
}

impl<T, I> Allocator<T, I>
where
    I: Iterator<Item = T>,
{
    fn new(items: I) -> Self {
        Self {
            fresh: items,
            clean: Vec::new(),
            dirty: VecDeque::new(),
        }
    }

    fn alloc_one(&mut self) -> Option<T> {
        self.clean
            .pop()
            .or_else(|| self.dirty.pop_front().or_else(|| self.fresh.next()))
    }

    fn alloc(&mut self, n: usize) -> Vec<T> {
        std::iter::from_fn(|| self.alloc_one()).take(n).collect()
    }

    fn free_clean<S>(&mut self, items: S)
    where
        S: Iterator<Item = T>,
    {
        self.clean.extend(items);
    }

    fn free_dirty<S>(&mut self, items: S)
    where
        S: Iterator<Item = T>,
    {
        self.dirty.extend(items);
    }
}

pub struct BitAllocator<'c> {
    class: Allocator<usize, RangeFrom<usize>>,
    quant: Allocator<usize, RangeFrom<usize>>,
    ctx: &'c Context<'c>,
}

impl<'c> BitAllocator<'c> {
    pub fn new(ctx: &'c Context) -> Self {
        Self {
            class: Allocator::new(0..),
            quant: Allocator::new(0..),
            ctx,
        }
    }

    /// Allocate space for a given type
    pub fn alloc_for_ty(&mut self, ty: TyId) -> BitSet {
        let sz = ty.size(self.ctx);
        BitSet {
            cbits: self.class.alloc(sz.csize),
            qbits: self.quant.alloc(sz.qsize),
        }
    }
}

impl<'a> Environment<'a> {
    pub fn bitset_ranges(&self, place: &Place) -> (ops::Range<Addr>, ops::Range<Addr>) {
        // start with the root type
        let mut ty = self.locals[place.root].ty;
        // traverse the allocation
        let (mut qi, mut ci) = (0, 0);
        for elem in &place.path {
            // TODO: [PERF] `ty.slot` should really return a `Slot` that also
            // contains an offset (and size?). These could be computed *once* when
            // the type is interned. This sort of "data about types" shouldn't
            // be computed *here*, of all place, and certainly not on every
            // call. In practice, it probably won't matter much, but it's really
            // bad in principle.
            for i in 0..*elem {
                // Actually, there's even more work being done here, because
                // `ty` is looked up repeatedly on *each* call to `slot`. There
                // are a *ton* of hashes going on here.
                let ty = ty.slot(i, self.ctx);
                let sz = ty.size(self.ctx);
                qi += sz.qsize;
                ci += sz.csize;
            }
            ty = ty.slot(*elem, self.ctx);
        }
        use crate::context::CtxDisplay;
        let sz = ty.size(self.ctx);
        let (qf, cf) = (qi + sz.qsize, ci + sz.csize);

        (qi..qf, ci..cf)
    }

    pub fn mem_copy(&mut self, lplace: &Place, rplace: &Place) {
        // NOTE: this actually *is* safe, and doesn't require an extra copy,
        // since we could always exclude the case `lplace == rplace`. But
        // proving that to the borrow checker sounds pretty daunting.
        let bits = self.bitset_at(rplace).to_owned();
        self.insert(lplace, bits.as_ref());
    }

    /// Get a sub-allocation at a place.
    pub fn bitset_at(&self, place: &Place) -> BitSetSlice {
        let ranges = self.bitset_ranges(place);
        let bitset = &self.get_entry(place.root).bits;
        bitset.index(ranges)
    }

    pub fn insert(&mut self, place: &Place, value: BitSetSlice) {
        let bits = &mut self.get_entry_mut(place.root).bits;
        bits.copy_from_slice(&value);
    }

    fn get_entry(&self, local: LocalId) -> &EnvEntry {
        &self.bindings[local]
    }

    fn get_entry_mut(&mut self, local: LocalId) -> &mut EnvEntry {
        &mut self.bindings[local]
    }
}

impl Default for EnvEntry {
    fn default() -> Self {
        Self {
            bits: BitSet::new(),
        }
    }
}

impl<'m> Interpreter<'m> {
    // Allocate space for a given place: this requires access to the graph in
    // the *current* stack frame, so this method can't (or shouldn't, without
    // introducing too much coupling) belong to the global allocator. The
    // problem here is that `Place` is borrowed (from `self.x`), so how will we
    // take `&mut self`?
    pub fn alloc_for_place(&mut self, place: &Place) -> BitSet {
        let ty = self.st.env.locals.type_of(&place, self.ctx);
        use crate::context::CtxDisplay;
        self.circ.alloc.alloc_for_ty(ty)
    }
}

/// A quantum or classical bit address
pub type Addr = usize;

/// An allocation of locally indexed virtual addresses
#[derive(Debug, Clone, Default)]
pub struct BitSet {
    pub qbits: Vec<Addr>,
    pub cbits: Vec<Addr>,
}

impl BitSet {
    pub fn new() -> Self {
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
            qbits: vec![0; sz.qsize],
            cbits: vec![0; sz.csize],
        }
    }

    pub fn append(&mut self, other: &mut BitSet) {
        self.qbits.append(&mut other.qbits);
        self.cbits.append(&mut other.cbits);
    }

    pub fn copy_from_slice(&mut self, slice: &BitSetSlice) {
        self.qbits.copy_from_slice(slice.qbits);
        self.cbits.copy_from_slice(slice.cbits);
    }

    pub fn as_ref(&self) -> BitSetSlice {
        BitSetSlice {
            qbits: &self.qbits,
            cbits: &self.cbits,
        }
    }

    // NOTE I don't think this can actually be done with the Index trait without
    // GATs.
    pub fn index<'b: 'a, 'a>(
        &'b self,
        idx: (std::ops::Range<Addr>, std::ops::Range<Addr>),
    ) -> BitSetSlice<'a> {
        BitSetSlice {
            qbits: &self.qbits[idx.0],
            cbits: &self.cbits[idx.1],
        }
    }

    pub fn index_mut<'b: 'a, 'a>(
        &'b mut self,
        idx: (std::ops::Range<Addr>, std::ops::Range<Addr>),
    ) -> BitSetSliceMut<'a> {
        BitSetSliceMut {
            qbits: &mut self.qbits[idx.0],
            cbits: &mut self.cbits[idx.1],
        }
    }
}

#[derive(Debug)]
pub struct BitSetSlice<'a> {
    pub qbits: &'a [Addr],
    pub cbits: &'a [Addr],
}

impl BitSetSlice<'_> {
    // NOTE should really use the ToOwned trait
    pub fn to_owned(&self) -> BitSet {
        BitSet {
            qbits: self.qbits.to_owned(),
            cbits: self.cbits.to_owned(),
        }
    }
}

pub struct BitSetSliceMut<'a> {
    pub qbits: &'a mut [Addr],
    pub cbits: &'a mut [Addr],
}
