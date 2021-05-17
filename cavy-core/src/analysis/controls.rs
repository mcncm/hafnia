use crate::{
    mir::*,
    store::{BitSet, Store},
};

use super::dominators::Dominators;

/// For each block, compute the blocks it's controlled by. Block B is
/// "controlled" by block A if A dominates B and B does not postdominate A.
pub fn control_blocks(
    dom: &Store<BlockId, Dominators>,
    postdom: &Store<BlockId, Dominators>,
) -> Store<BlockId, BitSet<BlockId>> {
    let mut controls = Store::new();
    for (blk, doms) in dom.idx_enumerate() {
        let mut ctrls = BitSet::empty(dom.len());
        for dom in doms.iter() {
            if !postdom[dom].contains(&blk) {
                *ctrls.get_mut(dom).unwrap() = true;
            }
        }
        controls.insert(ctrls);
    }
    controls
}

pub type ControlPlaces = Store<BlockId, Vec<(Place, bool)>>;

/// For each block, compute the `Places` it's controlled by, and which value(s)
/// that control takes on the branch. At the moment, we don't have ML-style
/// pattern matching, so these will always be booleans.
pub fn control_places(gr: &Graph, postdom: &Store<BlockId, Dominators>) -> ControlPlaces {
    let mut control_places = Store::new();

    let preds = gr.get_preds();
    // NOTE: we could compute this efficiently. But it's ok, we can just redo work
    // over and over, and do the O(n^2) thing where we follow each node all the way
    // up to the root.
    for (blk, _) in gr.idx_enumerate() {
        let mut curr = blk;
        let mut ctrls = vec![];
        // Controlling blocks are those that are dominators of our block, but
        // that our block does not postdominate. Therefore we can take *any*
        // path up the CFG, since that will give us every dominator.
        while let Some(prev) = preds[curr].first() {
            if !postdom[*prev].contains(&curr) {
                match &gr[*prev].kind {
                    BlockKind::Switch(switch) => {
                        let place = switch.cond.clone();
                        let branch = switch.blks.iter().enumerate().find(|(_, &blk)| blk == curr);
                        let (branch, _) = branch.unwrap();
                        let value = branch == 1; // *RIDICULOUS* hackery
                        ctrls.push((place, value));
                    }
                    _ => {
                        unreachable!("I assumed that block could not be postdominated")
                    }
                }
            }
            curr = *prev;
        }
        control_places.insert(ctrls);
    }

    control_places
}
