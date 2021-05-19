use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    analysis::{
        borrows::{
            self,
            regions::{LtId, RegionInf},
        },
        controls::{control_places, CtrlCond},
        dominators::DominatorAnalysis,
        Backward, DataflowCtx, DataflowRunner,
    },
    bitset,
    context::Context,
    mir::{Place, RvalueKind, Stmt, StmtKind},
    store::Store,
};

use crate::mir::{BlockId, Graph, GraphPt, LocalId};

/// Facts about the CFG that we need to know to do codegen
pub struct CfgFacts {
    pub controls: Store<BlockId, Vec<CtrlCond>>,
    pub uncompute_pts: BTreeMap<GraphPt, Vec<LocalId>>,
    // Extra, dubious things computed as "optimizations"
    /// Borrows that can share memory with the lender
    pub shared_mem_borrows: HashMap<LocalId, Place>,
}

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
pub fn cfg_facts(gr: &Graph, ctx: &Context) -> CfgFacts {
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

    let shared_mem = shared_mem_borrows(gr, &regions);

    CfgFacts {
        controls,
        uncompute_pts: pts,
        shared_mem_borrows: shared_mem,
    }
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
                let pt = GraphPt {
                    blk,
                    stmt: gr[blk].stmts.len(),
                };
                let lts = lts_at(pt, regions);
                lts
            })
            .fold(empty(regions), |acc, elem| acc | elem);
        // first statement looks at pred blocks
        let mut state = pred_lts;
        // Include the end of the block, which is not a real statement
        for loc in 0..block.len() {
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

// Another really useful thing to know is if a shared borrow is in fact the only
// one. If it is, we can reuse the memory of its referent. So only need to know
// if its lifetime intersects any *other* lifetime. We can compute this
// inefficiently, easily.
//
// * Get all the *loans* from the ascription store
// * Sort by loanee *super* coarsly. Take everything with the same root.
// * Take each one out, and... Actually, maybe don't even do that. Just use it
//   if it's the only one.
//
//   This will be... basically a fake optimization to make my circuits look better.
fn shared_mem_borrows<'a>(gr: &'a Graph, regions: &RegionInf) -> HashMap<LocalId, Place> {
    let mut uniq_locals = HashSet::new();
    let uniq_loan_places: HashSet<_> = regions
        .ascriptions
        .loans
        .iter()
        .map(|loan| &loan.place)
        // All right, let's get *RIDICULOUS*
        .filter(|pl| {
            if !uniq_locals.contains(&pl.root) {
                uniq_locals.insert(pl.root);
                true
            } else {
                false
            }
        })
        .collect();
    // *LITERALLY* copy-and-pasted from the enumerate_stmts function
    let stmts = gr
        .idx_enumerate()
        .map(|(blk, block)| {
            block.stmts.iter().enumerate().map(move |(pos, stmt)| {
                let loc = GraphPt { blk, stmt: pos };
                (loc, stmt)
            })
        })
        .flatten();

    let mut shared_mem_refs = HashMap::new();
    // and just take all the lhses from match some place whose root is only
    // borrowed once in the CFG.
    for (_, stmt) in stmts {
        match &stmt.kind {
            StmtKind::Assn(lhs, rhs) => match &rhs.data {
                RvalueKind::Ref(_, place) => {
                    if uniq_loan_places.contains(place) {
                        if lhs.path.is_empty() {
                            shared_mem_refs.insert(lhs.root, place.clone());
                        }
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    shared_mem_refs
}
