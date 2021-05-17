use std::collections::BTreeMap;

use crate::{
    analysis::{
        borrows::{
            self,
            regions::{LtId, RegionInf},
        },
        control_places,
        dominators::DominatorAnalysis,
        Backward, DataflowCtx, DataflowRunner,
    },
    bitset,
    context::Context,
    mir::Stmt,
};

use crate::mir::{Graph, GraphPt, LocalId};

// NOTE: this is really also where we should compute which controls are on which
// block, because blocks could also have been moved around.

/// Find the points at which references must be *uncomputed*. This function
/// will return a map that, at each point in the graph, lists all locals that we
/// need to uncompute at the end of the point.
///
/// Ok, maybe this is a weird way to do this, and a weird place to put it even
/// for the time being. But here's the reason: unlike in Rust, where lifetimes
/// are erased before codegen, we *fundamentally need* to know when they end,
/// because it's not a no-op. But, the optimization pass might well move things
/// around, change the sizes of blocks, add or remove locals, and so on. So
/// we're actually going to compute all the regions a *second time*, just to be
/// on the safe side and guard against subtle bugs due to any future
/// optimizations.
///
/// This requires going through enough of the "early" analyses to get a
/// `DataflowContext` again. No need to borrow check again, though.
///
/// Also, in any case, this might be a bit of an artifact of the style of
/// backend I'm using right now.
pub fn uncompute_points(gr: &Graph, ctx: &Context) -> BTreeMap<GraphPt, Vec<LocalId>> {
    let context = DataflowCtx::new(gr, ctx);

    // We'll need these again, too, in order to get our controls.
    let postdom = DominatorAnalysis::<Backward>::new(gr);
    let postdominators = DataflowRunner::new(postdom, &context).run().block_states;

    let controls = control_places(gr, &postdominators);

    let regions = borrows::regions::infer_regions(&context, &controls);

    let lt_ends = lifetime_ends(&regions, gr);
    let mut pts = BTreeMap::new();
    // Nothing like three nested loops to wake you up
    for (pt, lts) in lt_ends.iter() {
        let mut ending_locals = vec![];
        // this one is just to name the locals--*really* phoning it in now.
        // not to mention how horrendously inefficient this is.
        for (local, _) in regions.ascriptions.locals.idx_enumerate() {
            for ascr in regions.ascriptions.local_ascriptions(local) {
                if lts.contains(&ascr.lt) {
                    ending_locals.push(local);
                }
                break;
            }
        }
        if !ending_locals.is_empty() {
            pts.insert(*pt, ending_locals);
        }
    }
    pts
}

bitset! { Lifetimes(LtId) }

// Let's challenge ourselves to see how inefficiently we can do this: why not,
// compute everything twice.
//
// (really, this is here because I'm (probably) using the wrong data structure
// for lifetimes. They should be transposed.)
fn lifetime_ends(regions: &RegionInf, gr: &Graph) -> BTreeMap<GraphPt, Vec<LtId>> {
    let mut pts = BTreeMap::new();
    let preds = gr.get_preds();

    for (blk, block) in gr.idx_enumerate() {
        let pred_lts = preds[blk]
            .iter()
            .map(|&blk| {
                lts_at(
                    GraphPt {
                        blk,
                        stmt: gr[blk].len(),
                    },
                    regions,
                )
            })
            .fold(empty(regions), |acc, elem| acc & elem);
        // first statement looks at pred blocks
        let mut state = pred_lts;
        // Include the end of the block, which is not a real statement
        for loc in 0..=block.stmts.len() {
            let pt = GraphPt { blk, stmt: loc };
            let mut lts = vec![];
            let new_state = lts_at(pt, regions);
            let diff = state & !new_state.clone();
            for lt in diff.iter() {
                lts.push(lt);
            }
            if !lts.is_empty() {
                pts.insert(pt, lts);
            }
            state = new_state;
        }
    }
    pts
}

// Get the lifetimes at a point. This should probably just be reading from the
// lifetimes data structure
fn lts_at(pt: GraphPt, regions: &RegionInf) -> Lifetimes {
    let mut lts = empty(regions);
    for (lt, lifetime) in regions.lifetimes.idx_enumerate() {
        if lifetime.contains(&pt) {
            lts.set(lt, true);
        }
    }
    lts
}

fn empty(regions: &RegionInf) -> Lifetimes {
    Lifetimes::empty(regions.ascriptions.locals.len())
}
