use std::marker::PhantomData;

use crate::{context::Context, mir::*};

use super::*;

pub type Dominators = BitVec;

impl Lattice for Dominators {
    /// This is really "top".
    fn bottom(gr: &Graph, _ctx: &Context) -> Self {
        let blocks = gr.len();
        bitvec![1; blocks]
    }

    /// Intersect. This is really a "meet," not what you would call a join.
    fn join(self, other: Self) -> Self {
        self & other
    }
}

pub struct DominatorAnalysis<D: Direction> {
    _d: PhantomData<D>,
    blocks: usize,
}

impl<D: Direction> DominatorAnalysis<D> {
    pub fn new(gr: &Graph) -> Self {
        Self {
            _d: PhantomData,
            blocks: gr.len(),
        }
    }
}

impl<D: Direction> DataflowAnalysis<D, Blockwise> for DominatorAnalysis<D> {
    type Domain = Dominators;

    fn transfer_block(&self, _state: &mut Self::Domain, _block: &BlockKind, _loc: BlockId) {}

    fn initial_state(&self, blk: BlockId) -> Self::Domain {
        let mut bits = bitvec![0; self.blocks];
        *bits.get_mut(u32::from(blk) as usize).unwrap() = true;
        bits
    }

    fn join_predecessors<'a, I: Iterator<Item = (BlockId, &'a Self::Domain)>>(
        &self,
        blk: BlockId,
        preds: I,
    ) -> Self::Domain
    where
        Self::Domain: 'a,
    {
        let mut bits = DataflowAnalysis::<D, Blockwise>::join_predecessors_inner(self, blk, preds);
        *bits.get_mut(u32::from(blk) as usize).unwrap() = true;
        bits
    }
}
