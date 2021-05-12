use std::ops;

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
}

impl<'c> CircAssembler<'c> {
    fn alloc_class(&mut self, n: usize) -> Vec<Cbit> {
        let gates = &mut self.gate_buf;
        (&mut self.allocators.class)
            .take(n)
            .map(|bit| {
                gates.push(Inst::CInit(bit));
                bit
            })
            .collect()
    }

    fn alloc_quant(&mut self, n: usize) -> Vec<Qbit> {
        let gates = &mut self.gate_buf;
        (&mut self.allocators.quant)
            .take(n)
            .map(|bit| {
                gates.push(Inst::QInit(bit));
                bit
            })
            .collect()
    }

    /// Allocate space for a given type
    pub fn alloc_for_ty(&mut self, ty: TyId) -> BitArray {
        let sz = ty.size(self.ctx);
        BitArray {
            cbits: self.alloc_class(sz.csize),
            qbits: self.alloc_quant(sz.qsize),
        }
    }
}

impl<'a> MemFree<Qbit> for CircAssembler<'a> {
    fn free<S>(&mut self, items: S, state: FreeState)
    where
        S: Iterator<Item = Qbit>,
    {
        self.allocators.quant.free(items, state);
    }
}

impl<'a> MemFree<Cbit> for CircAssembler<'a> {
    fn free<S>(&mut self, items: S, state: FreeState)
    where
        S: Iterator<Item = Cbit>,
    {
        self.allocators.class.free(items, state);
    }
}

impl<'a> Environment<'a> {
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

    pub fn memcpy<B>(&mut self, left: &Place, right: &B)
    where
        B: AsBits,
    {
        let value = right.as_bits(self).to_owned();
        let bits = &mut self.bits_at_mut(left);
        bits.copy_from_slice(&value.as_ref());
    }

    /// Get a sub-allocation at a place.
    pub fn bits_at(&self, place: &Place) -> BitSlice {
        let ranges = self.bitset_ranges(place);
        let bitset = &self.get_entry(place.root).bits;
        bitset.index(ranges)
    }

    /// Get a sub-allocation at a place, mutably
    pub fn bits_at_mut(&mut self, place: &Place) -> BitSliceMut {
        let ranges = self.bitset_ranges(place);
        let bitset = &mut self.get_entry_mut(place.root).bits;
        bitset.index_mut(ranges)
    }

    fn get_entry<'b>(&'b self, local: LocalId) -> &'b EnvEntry<'a>
    where
        'a: 'b,
    {
        &self.bindings[local]
    }

    fn get_entry_mut<'b>(&'b mut self, local: LocalId) -> &'b mut EnvEntry<'a>
    where
        'a: 'b,
    {
        &mut self.bindings[local]
    }
}

impl Default for EnvEntry<'_> {
    fn default() -> Self {
        Self {
            bits: BitArray::new(),
            destructor: None,
        }
    }
}

impl<'m> Interpreter<'m> {
    // Allocate space for a given place: this requires access to the graph in
    // the *current* stack frame, so this method can't (or shouldn't, without
    // introducing too much coupling) belong to the global allocator. The
    // problem here is that `Place` is borrowed (from `self.x`), so how will we
    // take `&mut self`?
    //
    // NOTE: should this return a view of the allocated memory, rather than an
    // owned address array?
    pub fn alloc_for_place(&mut self, place: &Place) -> BitArray {
        let ty = self.st.env.locals.type_of(&place, self.ctx);
        let bitset = self.circ.alloc_for_ty(ty);
        self.st.env.memcpy(place, &bitset);
        bitset
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
            qbits: vec![Qbit::from(0); sz.qsize],
            cbits: vec![Cbit::from(0); sz.csize],
        }
    }

    pub fn append(&mut self, other: &mut BitArray) {
        self.qbits.append(&mut other.qbits);
        self.cbits.append(&mut other.cbits);
    }

    pub fn copy_from_slice(&mut self, slice: &BitSlice) {
        self.as_ref_mut().copy_from_slice(slice);
    }

    pub fn as_ref(&self) -> BitSlice {
        BitSlice {
            qbits: &self.qbits,
            cbits: &self.cbits,
        }
    }

    pub fn as_ref_mut(&mut self) -> BitSliceMut {
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

#[derive(Debug)]
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
    fn as_bits<'a>(&'a self, env: &'a Environment) -> BitSlice<'a>;
}

impl<'a> AsBits for BitSlice<'a> {
    fn as_bits<'b>(&'b self, _env: &'b Environment) -> BitSlice<'b> {
        Self {
            qbits: &self.qbits,
            cbits: &self.cbits,
        }
    }
}

impl AsBits for Place {
    fn as_bits<'a>(&'a self, env: &'a Environment) -> BitSlice<'a> {
        env.bits_at(self)
    }
}

impl AsBits for LocalId {
    fn as_bits<'a>(&'a self, env: &'a Environment) -> BitSlice<'a> {
        env.bits_at(&<Place>::from(*self))
    }
}

impl AsBits for BitArray {
    fn as_bits<'a>(&'a self, _env: &'a Environment) -> BitSlice<'a> {
        self.as_ref()
    }
}
