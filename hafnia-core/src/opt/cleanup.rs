//! This will clear out locals don't appear at all in the CFG, removing them
//! from the `LocalStore` and getting rid of their `Drop` statements.
//!
//! TODO locals renumbering

use std::collections::{HashMap, HashSet, VecDeque};

use smallvec::SmallVec;

use crate::{
    ast::IoDirection,
    context::Context,
    mir::*,
    place_tree::{PlaceNode, PlaceStore},
    store::{BitSet, Store},
};

use super::util::foreach_place;

use crate::analysis::{SummaryAnalysis, SummaryRunner};

pub fn optimize(mir: &mut Mir, ctx: &Context) {
    for gr in mir.graphs.iter_mut() {
        optimize_graph(gr, ctx);
    }
}

fn optimize_graph(gr: &mut Graph, ctx: &Context) {
    let mut used = LocalsUsed {
        used: BitSet::empty(gr.locals.len()),
    };

    SummaryRunner::new(gr, ctx, None).register(&mut used).run();
    cleanup_graph(gr, &used);
}

fn cleanup_graph(gr: &mut Graph, used: &LocalsUsed) {
    for block in gr.iter_mut() {
        for stmt in &mut block.stmts {
            cleanup_stmt(stmt, used);
        }
    }
    // NOTE: must run last: assumes that drops have already been cleaned up;
    // panics otherwise
    cleanup_locals(gr, used);
}

// Get rid of any unused locals from the graph's store
fn cleanup_locals(gr: &mut Graph, used: &LocalsUsed) {
    let old = std::mem::replace(&mut gr.locals, Store::new());
    // FIXME: must document or change this behavior. This is really surprising.
    let params = gr.nargs + 1;
    // for building a renumbering table
    let mut orig_ids = vec![];
    gr.locals
        .extend(old.into_iter().enumerate().filter_map(|(n, loc)| {
            let n_id = LocalId::from(n as u32);
            if n < params || used.contains(&n_id) {
                orig_ids.push(n_id);
                Some(loc)
            } else {
                None
            }
        }));

    let renum_table: HashMap<_, _> = orig_ids
        .drain(0..)
        .enumerate()
        .map(|(n, orig_id)| (orig_id, LocalId::from(n as u32)))
        .collect();

    foreach_place(gr, |pl| {
        pl.root = renum_table[&pl.root];
    });
}

fn cleanup_stmt(stmt: &mut Stmt, used: &LocalsUsed) {
    match &mut stmt.kind {
        StmtKind::Drop(local) if !used.contains(&local.root) => {
            stmt.kind = StmtKind::Nop;
        }
        _ => {}
    }
}

struct LocalsUsed {
    used: BitSet<LocalId>,
}

impl LocalsUsed {
    fn insert(&mut self, local: LocalId) {
        self.used.set(local, true);
    }

    fn contains(&self, local: &LocalId) -> bool {
        self.used.contains(local)
    }
}

impl SummaryAnalysis for LocalsUsed {
    fn trans_stmt(&mut self, stmt: &Stmt, _loc: &GraphPt) {
        use StmtKind::*;
        match &stmt.kind {
            Assn(lhs, rv) => {
                self.insert(lhs.root);
                for pl in rv.places() {
                    self.insert(pl.root);
                }
            }
            Assert(pl) => {
                self.insert(pl.root);
            }
            Drop(_) => {}
            Io(io) => match &io.dir {
                IoDirection::In => todo!(),
                IoDirection::Out => {
                    self.insert(io.place.root);
                }
            },
            Nop => {}
        }
    }

    fn trans_block(&mut self, block: &BlockKind, _loc: &BlockId) {
        match block {
            BlockKind::Goto(_) => {}
            BlockKind::Switch(switch) => {
                self.insert(switch.cond.root);
            }
            BlockKind::Call(call) => {
                self.insert(call.ret.root);
                for arg in &call.args {
                    arg.place().map(|pl| self.insert(pl.root));
                }
            }
            BlockKind::Ret => {}
        }
    }
}
