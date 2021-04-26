use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::{cell::Ref, collections::hash_map::Entry};

use mir::Stmt;

use crate::{ast::FnId, context::Context, mir::*};
use crate::{cavy_errors::ErrorBuf, mir, store::Store};

pub trait Direction {}

/// Marker type for forward-flowing dataflow analyses
pub struct Forward;
impl Direction for Forward {}

/// Marker type for backward-flowing dataflow analyses
pub struct Backward;
impl Direction for Backward {}

/// The main trait for analysis data, representing a join-semilattice.
pub trait Lattice: Clone + PartialEq + Eq {
    fn join(&self, other: &Self) -> Self;

    fn bottom(gr: &Graph, ctx: &Context) -> Self;
}

/// Any set forms a join-semilattice under unions.
impl<T> Lattice for HashSet<T>
where
    T: Clone + Eq + Hash,
{
    fn join(&self, other: &Self) -> Self {
        self.union(other).cloned().collect()
    }

    fn bottom(_gr: &Graph, _ctx: &Context) -> Self {
        Self::new()
    }
}

impl<K, V> Lattice for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone + Eq,
{
    fn join(&self, other: &Self) -> Self {
        let mut new = self.clone();
        new.extend(other.clone());
        new
    }

    fn bottom(_gr: &Graph, _ctx: &Context) -> Self {
        Self::new()
    }
}

/// Trait for a general dataflow analysis
pub trait DataflowAnalysis<'mir, 'ctx, D>
where
    D: Direction,
{
    type Domain: Lattice;

    /// Apply the transfer function for a single statement
    fn trans_stmt(&self, state: &mut Self::Domain, stmt: &Stmt, data: &mir::BlockData);

    /// Apply the transfer function for the end of a basic block
    fn trans_block(&self, state: &mut Self::Domain, block: &BlockKind, data: &mir::BlockData);
}

/// The state of an an analysis on entry into each block.
///
/// NOTE Improvements that could be made: this is a good example of where we
/// could (potentially) benefit from using persistent data structures. Also,
/// rustc doesn't enforce generic parameters in type aliases. That makes this
/// alias a little less constraining than it really should be. I think it also
/// might be better to store the state on *exit* from each block. It eliminates
/// the need to store a separate `exit_state`, eliminates the redundancy of the
/// starting states at a switch, and eliminates the zero-information starting
/// state at the entry block.
#[derive(Debug)]
pub struct AnalysisStates<L: Lattice> {
    /// The state on entry to each block
    pub entry_states: Store<mir::BlockId, L>,
    /// The state on return from the procedure
    pub exit_state: L,
}

pub trait SuccGetter<'a> {
    fn new(preds: Ref<'a, Store<BlockId, Vec<BlockId>>>) -> Self;

    fn successors<'b>(&'b self, _blk_id: BlockId, block: &'b BasicBlock) -> &'b [BlockId] {
        block.successors()
    }
}

/// A helper struct to satisfy the borrow checker: used to compute the
/// successors to a node.
pub struct Successors<'a, D: Direction> {
    preds: Ref<'a, Store<BlockId, Vec<BlockId>>>,
    _d: D,
}

impl<'a> SuccGetter<'a> for Successors<'a, Forward> {
    fn new(preds: Ref<'a, Store<BlockId, Vec<BlockId>>>) -> Self {
        Self {
            preds,
            _d: Forward {},
        }
    }

    /// It looks silly, but this has both arguments because we have access to
    /// the `Block` going forwards, and only the `BlockId` going backwards.
    fn successors<'b>(&'b self, _blk_id: BlockId, block: &'b BasicBlock) -> &'b [BlockId] {
        block.successors()
    }
}

impl<'a> SuccGetter<'a> for Successors<'a, Backward> {
    fn new(preds: Ref<'a, Store<BlockId, Vec<BlockId>>>) -> Self {
        Self {
            preds,
            _d: Backward {},
        }
    }

    /// It looks silly, but this has both arguments because we have access to
    /// the `Block` going forwards, and only the `BlockId` going backwards.
    fn successors(&self, blk_id: BlockId, _block: &BasicBlock) -> &[BlockId] {
        &self.preds[blk_id]
    }
}

/// An execution environment for a dataflow analysis, using the Killdall method.
///
/// NOTE Can we do this with a *single* pass per direction? Can we do it without
/// generics? Probably only if we store the results in the analysis types
/// themselves.
pub struct DataflowRunner<'mir, 'ctx, A, D>
where
    A: DataflowAnalysis<'mir, 'ctx, D>,
    D: Direction,
    Successors<'mir, D>: SuccGetter<'mir>,
{
    analysis: A,
    results: AnalysisStates<A::Domain>,
    gr: &'mir mir::Graph,
    succs: Successors<'mir, D>,
    ctx: &'mir Context<'ctx>,
    /// The next set of blocks to be analyzed
    working_set: HashSet<BlockId>,
}

impl<'mir, 'ctx, A, D> DataflowRunner<'mir, 'ctx, A, D>
where
    A: DataflowAnalysis<'mir, 'ctx, D>,
    D: Direction,
    Self: Propagate<'mir, 'ctx, A, D>,
    Successors<'mir, D>: SuccGetter<'mir>,
{
    pub fn new(analysis: A, gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        let succs = Successors::new(gr.get_preds());
        let bot = A::Domain::bottom(gr, ctx);
        // FIXME this is doing a lot of extra work to fill in these "default"
        // values. Maybe we should use either a `Store<BlockId,
        // Option<A::Domain>>` or a `HashMap<BlockId, A::Domain>`, or somehow
        // guarantee that we walk the blocks in index-order.
        let entry_states = std::iter::repeat(bot.clone()).take(gr.len()).collect();
        let exit_state = bot;
        let results = AnalysisStates {
            entry_states,
            exit_state,
        };
        let mut working_set = HashSet::new();
        working_set.insert(gr.entry_block);
        Self {
            analysis,
            results,
            gr,
            ctx,
            succs,
            working_set,
        }
    }

    pub fn run(mut self) -> AnalysisStates<A::Domain> {
        while !self.working_set.is_empty() {
            let working_set: Vec<_> = self.working_set.drain().collect();
            for block in working_set {
                self.run_inner(block);
            }
        }
        self.results
    }

    /// Update the state associated with a single block. We'll take the previous
    /// entry state, propagate it, and compare the exit state to the entry
    /// states of any successor block. If they differ, they are updated and
    /// these blocks are entered into the working set. We'll also take any
    /// action associated with the block kind.
    fn run_inner(&mut self, blk_id: BlockId) {
        let mut state = self.results.entry_states[blk_id].clone();
        let block = &self.gr[blk_id];
        self.propagate(&mut state, &block);

        // Compute the successor blocks and do any extra block-kind-dependent work.
        if let BlockKind::Ret = block.kind {
            self.results.exit_state = self.results.exit_state.join(&state);
        }
        let succs = self.succs.successors(blk_id, block);

        // If the propagated state differs from that of any successor, enter it
        // into the working set.
        for succ in succs {
            let prev_succ_state = &mut self.results.entry_states[*succ];
            let succ_state = prev_succ_state.join(&state);
            if &succ_state != prev_succ_state {
                *prev_succ_state = succ_state;
                self.working_set.insert(*succ);
            }
        }
    }
}

pub trait Propagate<'m, 'c, A, D>
where
    A: DataflowAnalysis<'m, 'c, D>,
    D: Direction,
{
    fn propagate(&mut self, state: &mut A::Domain, block: &BasicBlock);
}

impl<'m, 'c, A> Propagate<'m, 'c, A, Forward> for DataflowRunner<'m, 'c, A, Forward>
where
    A: DataflowAnalysis<'m, 'c, Forward>,
{
    /// Apply the transfer function of a block, which is just the composition of
    /// the transfer functions of its statements. Begin with the state-on-entry,
    /// set the result value to this state, and mutate the state through the block.
    fn propagate(&mut self, state: &mut A::Domain, block: &BasicBlock) {
        for stmt in block.stmts.iter() {
            self.analysis.trans_stmt(state, stmt, &block.data);
        }
        self.analysis.trans_block(state, &block.kind, &block.data);
    }
}

impl<'m, 'c, A> Propagate<'m, 'c, A, Backward> for DataflowRunner<'m, 'c, A, Backward>
where
    A: DataflowAnalysis<'m, 'c, Backward>,
{
    /// Apply the transfer function of a block, which is just the composition of
    /// the transfer functions of its statements. Begin with the state-on-entry,
    /// set the result value to this state, and mutate the state through the block.
    fn propagate(&mut self, state: &mut A::Domain, block: &BasicBlock) {
        self.analysis.trans_block(state, &block.kind, &block.data);
        for stmt in block.stmts.iter().rev() {
            self.analysis.trans_stmt(state, stmt, &block.data);
        }
    }
}

// == Summary analyses ==

/// A simple analysis that makes only a single pass over all blocks, *regardless
/// of the graph topology*, and that only needs to track a single (therefore
/// non-block-local) instance of the analysis state.
pub trait SummaryAnalysis {
    /// Apply the transfer function for a single statement
    fn trans_stmt(&mut self, stmt: &Stmt, loc: &GraphLoc);

    /// Apply the transfer function for the end of a basic block
    fn trans_block(&mut self, block: &BlockKind, loc: &BlockId);

    /// If this analysis identified any errors, check for them
    fn check(&self, _errs: &mut ErrorBuf) {}

    /// Some analyses might turn themselves off on certain inputs
    fn enabled(&self) -> bool {
        true
    }
}

/// An execution environment for simple analyses.
pub struct SummaryRunner<'a> {
    fn_id: FnId,
    gr: &'a mir::Graph,
    errs: &'a mut ErrorBuf,
    ctx: &'a Context<'a>,
    analyses: Vec<&'a mut dyn SummaryAnalysis>,
}

// NOTE that we might eventually want `SummaryRunner` and `DataflowRunner` to
// implement some common trait.
impl<'a> SummaryRunner<'a> {
    pub fn new(fn_id: FnId, gr: &'a Graph, ctx: &'a Context, errs: &'a mut ErrorBuf) -> Self {
        Self {
            fn_id,
            gr,
            errs,
            ctx,
            analyses: Vec::new(),
        }
    }

    pub fn register(mut self, analysis: &'a mut dyn SummaryAnalysis) -> Self {
        if analysis.enabled() {
            self.analyses.push(analysis);
        }
        self
    }

    pub fn run(mut self) {
        for (blk_id, blk) in self.gr.idx_enumerate() {
            for (pos, stmt) in blk.stmts.iter().enumerate() {
                let loc = GraphLoc {
                    blk: blk_id,
                    stmt: pos,
                };
                // Struggling to unify these two loops with an observer pattern
                // here. How do I do that with only `&mut dyn Trait`s?
                for ana in &mut self.analyses {
                    ana.trans_stmt(stmt, &loc);
                }
            }
            for ana in &mut self.analyses {
                ana.trans_block(&blk.kind, &blk_id);
            }
        }
        self.check();
    }

    fn check(&mut self) {
        for ana in &mut self.analyses {
            ana.check(&mut self.errs);
        }
    }
}
