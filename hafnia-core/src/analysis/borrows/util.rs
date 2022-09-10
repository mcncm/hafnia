//! Some functions that might prove more generally useful for the module. Maybe
//! I'll keep them here; maybe I'll demote them to other submodules if they're
//! only used in one place.

use crate::mir::*;

/// Walk all the statements of the CFG, in no particular order.
///
/// NOTE: This function is probably *usually* dangerous to use, especially if
/// you're just trying to enumerate all the points in the graph. Because
/// statementwise dataflow analyses have points for block tails, this will miss
/// points. The case where you might want it is where you're also, separately,
/// iterating over block tails. But you probably want `DataflowCtx::iter_pts`.
pub fn enumerate_stmts(gr: &Graph) -> impl Iterator<Item = (GraphPt, &Stmt)> {
    gr.idx_enumerate().flat_map(|(blk, block)| {
        block.stmts.iter().enumerate().map(move |(pos, stmt)| {
            let loc = GraphPt { blk, stmt: pos };
            (loc, stmt)
        })
    })
}

pub fn enumerate_tails(gr: &Graph) -> impl Iterator<Item = (GraphPt, &BlockKind)> {
    gr.idx_enumerate().map(|(blk, block)| {
        let pt = GraphPt {
            blk,
            stmt: block.len(),
        };
        (pt, &block.kind)
    })
}
