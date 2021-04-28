use std::ops;

use crate::{
    circuit::FreeState,
    types::{TyId, TypeSize},
};

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
        let bit = self.clean.pop().or_else(|| self.fresh.next());
        bit
    }

    fn alloc(&mut self, n: usize) -> Vec<T> {
        std::iter::from_fn(|| self.alloc_one()).take(n).collect()
    }

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

/// Specifier for a qubit set
pub enum BitKind {}

pub struct BitAllocator<'c> {
    class: Allocator<usize, RangeFrom<usize>>,
    quant: Allocator<usize, RangeFrom<usize>>,
    // NOTE: This struct *could* just hold onto the type interner. But
    // `Ty::size_inner` isn't `pub`, so I'll give it access to the whole
    // `Context` for now.
    ctx: &'c Context<'c>,
}

///

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

    pub fn free_class<S: Iterator<Item = Addr>>(&mut self, items: S, state: FreeState) {
        self.class.free(items, state);
    }

    pub fn free_quant<S: Iterator<Item = Addr>>(&mut self, items: S, state: FreeState) {
        self.quant.free(items, state);
    }

    pub fn free(&mut self, bits: BitSetSlice, state: FreeState) {
        self.free_class(bits.cbits.iter().copied(), state);
        self.free_quant(bits.qbits.iter().copied(), state);
    }
}

impl<'a> CircAssembler<'a> {}

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
        let sz = ty.size(self.ctx);
        let (qf, cf) = (qi + sz.qsize, ci + sz.csize);

        (qi..qf, ci..cf)
    }

    pub fn mem_copy(&mut self, lplace: &Place, rplace: &Place) {
        // NOTE: this actually *is* safe, and doesn't require an extra copy,
        // since we could always exclude the case `lplace == rplace`. But
        // proving that to the borrow checker sounds pretty daunting.
        let bits = self.bits_at(rplace).to_owned();
        self.insert(lplace, bits.as_ref());
    }

    /// Get a sub-allocation at a place.
    pub fn bits_at(&self, place: &Place) -> BitSetSlice {
        let ranges = self.bitset_ranges(place);
        let bitset = &self.get_entry(place.root).bits;
        bitset.index(ranges)
    }

    /// Get a sub-allocation at a place, mutably
    pub fn bits_at_mut(&mut self, place: &Place) -> BitSetSliceMut {
        let ranges = self.bitset_ranges(place);
        let bitset = &mut self.get_entry_mut(place.root).bits;
        bitset.index_mut(ranges)
    }

    pub fn insert(&mut self, place: &Place, value: BitSetSlice) {
        let bits = &mut self.bits_at_mut(place);
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
        let bitset = self.circ.alloc.alloc_for_ty(ty);
        bitset
    }
}

// NOTE: it has already caused some slight problems that these are untyped. It
// might really make sense to wrap them.
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
        self.as_ref_mut().copy_from_slice(slice);
    }

    pub fn as_ref(&self) -> BitSetSlice {
        BitSetSlice {
            qbits: &self.qbits,
            cbits: &self.cbits,
        }
    }

    pub fn as_ref_mut(&mut self) -> BitSetSliceMut {
        BitSetSliceMut {
            qbits: &mut self.qbits,
            cbits: &mut self.cbits,
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

impl<'a> BitSetSliceMut<'a> {
    fn copy_from_slice(&mut self, other: &BitSetSlice) {
        self.qbits.copy_from_slice(other.qbits);
        self.cbits.copy_from_slice(other.cbits);
    }
}
