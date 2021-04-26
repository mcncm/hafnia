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

    fn free_clean(&mut self, item: T) {
        self.clean.push(item);
    }

    fn free_dirty(&mut self, item: T) {
        self.dirty.push_back(item);
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
            cbits: self.class.alloc(sz.qsize),
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

    /// Get a sub-allocation at a place.
    pub fn bitset_at(&self, place: &Place) -> BitSetSlice {
        let ranges = self.bitset_ranges(place);
        let bitset = &self.get(&place.root).bits;
        bitset.index(ranges)
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
