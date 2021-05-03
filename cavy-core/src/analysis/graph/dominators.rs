use std::marker::PhantomData;

use crate::{context::Context, mir::*, store::BitSet};

use super::*;

#[derive(Clone, PartialEq, Eq)]
pub struct Dominators(BitSet<BlockId>);

impl Lattice for Dominators {
    /// This is really "top".
    fn bottom(gr: &Graph, _ctx: &Context) -> Self {
        let blocks = gr.len();
        Self(BitSet::full(blocks))
    }

    /// Intersect. This is really a "meet," not what you would call a join.
    fn join(self, other: Self) -> Self {
        Dominators(self.0 & other.0)
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
        Dominators(BitSet::from(bits))
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
        *bits.0.get_mut(blk).unwrap() = true;
        bits
    }
}

// == Some dominator-related computations ==

/// For each block, compute the blocks it's controlled by. Block B is
/// "controlled" by block A if A dominates B and B does not postdominate A.
pub fn controls(
    dom: &Store<BlockId, Dominators>,
    postdom: &Store<BlockId, Dominators>,
) -> Store<BlockId, BitSet<BlockId>> {
    let mut controls = Store::new();
    for (blk, doms) in dom.idx_enumerate() {
        let mut ctrls = BitSet::empty(dom.len());
        for dom in doms.0.iter() {
            if !postdom[dom].0.contains(&blk) {
                *ctrls.get_mut(dom).unwrap() = true;
            }
        }
        controls.insert(ctrls);
    }
    controls
}
