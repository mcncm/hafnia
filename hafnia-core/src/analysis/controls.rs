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

/// A control condition on a `Place` appearing in some classical control
/// structure.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CtrlCond {
    pub place: Place,
    pub value: bool,
}

pub type ControlPlaces = Store<BlockId, Vec<CtrlCond>>;

/// For each block, compute the `Places` it's controlled by, and which value(s)
/// that control takes on the branch. At the moment, we don't have ML-style
/// pattern matching, so these will always be booleans.
pub fn control_places(gr: &Graph, _postdom: &Store<BlockId, Dominators>) -> ControlPlaces {
    let mut control_places = Store::new();

    let preds = gr.get_preds();
    // FIXME: this algorithm is just not correct
    for (blk, _) in gr.idx_enumerate() {
        let mut curr = blk;
        let mut ctrls = vec![];
        let mut merges: u32 = 0;
        while let Some(prev) = preds[curr].first() {
            if preds[curr].len() > 1 {
                merges += 1;
            }
            if let BlockKind::Switch(switch) = &gr[*prev].kind {
                if merges == 0 {
                    let place = switch.cond.clone();
                    let branch = switch.blks.iter().enumerate().find(|(_, &blk)| blk == curr);
                    let (branch, _) = branch.unwrap();
                    let value = branch == 1; // *RIDICULOUS* hackery
                    ctrls.push(CtrlCond { place, value });
                }

                merges = merges.saturating_sub(1);
            } else {
                unreachable!("I assumed that block could not be postdominated")
            }
            curr = *prev;
        }
        control_places.insert(ctrls);
    }

    control_places
}
