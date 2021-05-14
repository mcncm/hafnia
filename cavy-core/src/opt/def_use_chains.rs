//! Eliminate locals that would generate superfluous SWAPs and controls by
//! chaining unary statements.
//!
//! We should almost certainly be doing the proper thing in SSA. Instead, we'll
//! use a really hacky flow-insensitive algorithm that will be good *enough* to
//! make decent-looking circuit diagrams for the report. Here's what it is:
//!
//! * Walk over the whole CFG and collect and, in a *summary* analysis, collect
//!   the definition site(s) and use site(s) of each `Place`.
//!
//! * Collect all the pairs with exactly one definition site and one use site
//!   into a hash table.
//!
//! * Walk chains in the table to find the endpoints, and stitch together
//!   everything in-between.
//!
//! This will fall over on trivial examples the *should* work. But this could
//! even be made a little more sophisticated before even doing the "real" thing.
//!
//! TODO: actually, are cycles possible here?
//!
//! TODO: there's something not quite right here in that an RHS could use the
//! same value multiple times, and *that* would be fine.

use std::collections::{HashMap, HashSet, VecDeque};

use smallvec::SmallVec;

use crate::{
    context::Context,
    mir::*,
    place_tree::{PlaceNode, PlaceStore},
};

use crate::analysis::{SummaryAnalysis, SummaryRunner};

pub fn optimize(mir: &mut Mir, _ctx: &Context) {
    for gr in mir.graphs.iter_mut() {
        optimize_graph(gr);
    }
}

fn optimize_graph(gr: &mut Graph) {
    // First, check where everything is defined and used.
    let use_data = collect_uses(gr);
    // Then find everything that has only a single definition and use, and
    // collect it into a hash table so we can build some chains.
    //
    // TODO: clean up this mess, it's hard to read
    let single_def_use: HashMap<_, _> = use_data
        .iter()
        .map(|tree| {
            tree.iter_post().filter_map(|data| {
                // Drops only count as a use if there is no other use
                if data.defs.len() == 1 {
                    if data.uses.len() == 1 {
                        Some((data.defs[0], data.uses[0]))
                    } else if let Some(drop) = data.drop {
                        Some((data.defs[0], drop))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
        })
        .flatten()
        .collect();
    // Next, build the chains.
    let chains = build_chains(single_def_use);
    // And then *apply* the chains to rewrite the graph.
    for chain in chains.into_iter() {
        apply_defuse_chain(gr, chain);
    }
}

fn apply_defuse_chain(gr: &mut Graph, mut chain: Vec<GraphPt>) {
    // At this point, we have a chain of matching defs and uses, and we want to
    // rewrite every `Place` that appears after the first to equal the lhs of
    // the first.
    let last = chain.pop().expect("at least one element per chain");
    let mut chain = chain.into_iter();
    let first = match chain.next() {
        Some(pt) => pt,
        None => return,
    };
    let place = get_lhs_at(gr, first).unwrap();
    let mut prev = place.clone();
    for pt in chain {
        prev = replace_places_at(gr, pt, &place, &prev, false)
            .expect("mid-chain points should have an lhs");
    }
    replace_places_at(gr, last, &place, &prev, true);
}

/// `replace_lhs` true if the left-hand-side should be replaced; false if only the rhs
/// should be replaced. If not the last in the chain, return the 'def' that was just replaced.
fn replace_places_at(
    gr: &mut Graph,
    pt: GraphPt,
    place: &Place,
    prev: &Place,
    last: bool,
) -> Option<Place> {
    let block = &mut gr[pt.blk];
    if pt.stmt < block.stmts.len() {
        let stmt = &mut block.stmts[pt.stmt];
        use StmtKind::*;
        match &mut stmt.kind {
            Assn(lhs, rhs) => {
                replace_places_rv(rhs, place, prev);
                if !last {
                    return Some(std::mem::replace(lhs, place.clone()));
                }
            }
            Assert(pl) => *pl = place.clone(),
            // Unused drops will get cleaned up later
            Drop(_) => {}
            Io(io) => match io {
                IoStmtKind::In => todo!(),
                IoStmtKind::Out { place: pl, .. } => {
                    *pl = place.clone();
                }
            },
            Nop => unreachable!(),
        }
    } else {
        debug_assert_eq!(pt.stmt, block.stmts.len());
        use BlockKind::*;
        match &mut block.kind {
            Call(call) => {
                for arg in call.args.iter_mut() {
                    replace_place_op(arg, place, &prev);
                }
                if !last {
                    debug_assert_eq!(call.args.len(), 1);
                    return Some(std::mem::replace(&mut call.ret, place.clone()));
                }
            }
            Goto(_) => {}
            Switch(switch) => {
                switch.cond = place.clone();
            }
            Ret => {}
        }
    };
    None
}

fn replace_places_rv(rv: &mut Rvalue, place: &Place, prev: &Place) {
    use RvalueKind::*;
    match &mut rv.data {
        BinOp(_, lop, rop) => {
            replace_place_op(lop, place, prev);
            replace_place_op(rop, place, prev);
        }
        UnOp(_, op) | Use(op) => replace_place_op(op, place, prev),
        Ref(_, pl) => *pl = place.clone(),
    }
}

fn replace_place_op(op: &mut Operand, place: &Place, prev: &Place) {
    match op {
        Operand::Copy(pl) | Operand::Move(pl) if pl == prev => {
            *pl = place.clone();
        }
        _ => {}
    }
}

fn get_lhs_at(gr: &Graph, pt: GraphPt) -> Option<Place> {
    let block = &gr[pt.blk];
    if pt.stmt < block.stmts.len() {
        let stmt = &block.stmts[pt.stmt];
        match &stmt.kind {
            StmtKind::Assn(lhs, _) => Some(lhs.clone()),
            _ => unreachable!(),
        }
    } else {
        debug_assert_eq!(pt.stmt, block.stmts.len());
        match &block.kind {
            BlockKind::Call(call) => Some(call.ret.clone()),
            _ => unreachable!(),
        }
    }
}

/// Turn all the use-def pairs into contiguous chains of graph points
fn build_chains(mut def_use: HashMap<GraphPt, GraphPt>) -> Vec<Vec<GraphPt>> {
    let mut chains: Vec<Vec<GraphPt>> = vec![];
    // the defs that at the front of some chain
    let mut heads = HashMap::<GraphPt, usize>::new();
    // the uses that are at the back of some chain
    let mut tails = HashMap::<GraphPt, usize>::new();
    while let Some((def, mut use_)) = pop_map(&mut def_use) {
        // we could be starting a new chain, or attaching at the head or tail of
        // an existing chain. We'll eventually run out of elements and make a
        // new chain, or attach.
        let mut ch = vec![def];
        while let Some((next_def, next_use)) = def_use.remove_entry(&use_) {
            ch.push(next_def);
            use_ = next_use;
        }
        ch.push(use_);

        // Once we're done with the chain, try to attach it. Start by looking
        // for a tail to attach it to...
        if let Some((_, idx)) = tails.remove_entry(&def) {
            tails.insert(use_, idx);
            let chain = &mut chains[idx];
            chain.pop();
            chain.extend(ch);
        }
        //...and then a head.
        //
        // NOTE: it shouldn't be possible for *both* of these to happen, unless
        // there's a cycle.
        else if let Some((_, idx)) = heads.remove_entry(&use_) {
            heads.insert(def, idx);
            let chain = &mut chains[idx];
            std::mem::swap(chain, &mut ch);
            chain.pop();
            chain.extend(ch);
        }
        // Othewise, just make a new chain.
        else {
            tails.insert(*ch.last().unwrap(), chains.len());
            heads.insert(ch[0], chains.len());
            chains.push(ch.drain(0..).collect());
        }
    }
    chains
}

fn pop_map<K, V>(map: &mut HashMap<K, V>) -> Option<(K, V)>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    let elem = map.iter().next().map(|kv| (kv.0.clone(), kv.1.clone()));
    elem.as_ref().map(|elem| map.remove(&elem.0));
    elem
}

fn collect_uses(gr: &Graph) -> PlaceStore<UseData> {
    let mut use_data = PlaceStore::new(gr.locals.len());
    for (blk, block) in gr.idx_enumerate() {
        let mut loc = 0;
        for stmt in block.stmts.iter() {
            let pt = GraphPt { blk, stmt: loc };
            collect_stmt(&mut use_data, &stmt.kind, pt);
            loc += 1;
        }
        let pt = GraphPt { blk, stmt: loc };
        collect_tail(&mut use_data, &block.kind, pt);
    }
    use_data
}

fn collect_stmt(use_data: &mut PlaceStore<UseData>, stmt: &StmtKind, pt: GraphPt) {
    use RvalueKind::*;
    match stmt {
        StmtKind::Assn(lhs, rhs) => {
            match &rhs.data {
                BinOp(_, fst, snd) => {
                    use_operand(use_data, fst, pt);
                    use_operand(use_data, snd, pt);
                }
                UnOp(_, op) | Use(op) => use_operand(use_data, op, pt),
                Ref(_, place) => {
                    insert_action(use_data, place, pt, Action::Use);
                    // Don't collect an action for the lhs
                    return;
                }
            }
            insert_action(use_data, lhs, pt, Action::Def);
        }
        StmtKind::Assert(place) => {
            insert_action(use_data, place, pt, Action::Use);
        }
        StmtKind::Drop(place) => {
            insert_action(use_data, place, pt, Action::Drop);
        }
        StmtKind::Io(io) => {
            let place = match io {
                IoStmtKind::In => todo!(),
                IoStmtKind::Out { place, .. } => place,
            };
            insert_action(use_data, place, pt, Action::Use);
        }
        StmtKind::Nop => {}
    }
}

fn collect_tail(use_data: &mut PlaceStore<UseData>, tail: &BlockKind, pt: GraphPt) {
    match tail {
        BlockKind::Goto(_) => {}
        BlockKind::Ret => {}
        BlockKind::Switch(switch) => {
            insert_action(use_data, &switch.cond, pt, Action::Use);
        }
        BlockKind::Call(call) => {
            insert_action(use_data, &call.ret, pt, Action::Def);
            for arg in &call.args {
                use_operand(use_data, arg, pt);
            }
        }
    }
}

fn use_operand(use_data: &mut PlaceStore<UseData>, op: &Operand, pt: GraphPt) {
    match op {
        Operand::Const(_) | Operand::Copy(_) => {}
        Operand::Move(place) => {
            insert_action(use_data, place, pt, Action::Use);
        }
    }
}

enum Action {
    Def,
    Use,
    Drop,
}

fn insert_action(use_data: &mut PlaceStore<UseData>, place: &Place, pt: GraphPt, action: Action) {
    let node = use_data.create_node(place);
    let data = node.this.get_or_insert_with(|| UseData::default());
    match action {
        Action::Def => data.defs.push(pt),
        Action::Use => data.uses.push(pt),
        Action::Drop => data.drop = Some(pt),
    }
}

#[derive(Default)]
struct UseData {
    /// The definition sites
    defs: SmallVec<[GraphPt; 1]>,
    /// The *unary* statements in which this appears as an RHS
    uses: SmallVec<[GraphPt; 1]>,
    drop: Option<GraphPt>,
}
