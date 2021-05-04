//! Some functions that might prove more generally useful for the module. Maybe
//! I'll keep them here; maybe I'll demote them to other submodules if they're
//! only used in one place.

use crate::mir::*;

/// Walk all the statements of the CFG, in no particular ordere
pub fn enumerate_stmts(gr: &Graph) -> impl Iterator<Item = (GraphLoc, &Stmt)> {
    gr.idx_enumerate()
        .map(|(blk, block)| {
            block.stmts.iter().enumerate().map(move |(pos, stmt)| {
                let loc = GraphLoc { blk, stmt: pos };
                (loc, stmt)
            })
        })
        .flatten()
}
