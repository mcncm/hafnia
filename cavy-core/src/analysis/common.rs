use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::{cavy_errors::ErrorBuf, mir, store::Store};
use crate::{context::Context, mir::*};

/// Marker type for forward-flowing dataflow analyses
pub struct Forward;

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
pub trait Analysis<'mir, 'ctx> {
    type Direction;
    type Domain: Lattice;

    /// Apply the transfer function for a single statement
    fn trans_stmt(&self, state: &mut Self::Domain, stmt: &mir::Stmt, data: &mir::BlockData);

    /// Apply the transfer function for the end of a basic block
    fn trans_block(&self, state: &mut Self::Domain, block: &BlockKind, data: &mir::BlockData);

    // FIXME Instead of making a new runner for each analysis, consider
    // registering all analyses with a single runner.
    fn into_runner(
        self,
        ctx: &'mir Context<'ctx>,
        gr: &'mir Graph,
    ) -> DataflowRunner<'mir, 'ctx, Self>
    where
        Self: Sized,
    {
        DataflowRunner::new(self, gr, ctx)
    }
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

/// An execution environment for a dataflow analysis, using the Killdall method.
///
/// NOTE Can we do this with a *single* pass per direction? Can we do it without
/// generics? Probably only if we store the results in the analysis types
/// themselves.
pub struct DataflowRunner<'mir, 'ctx, A>
where
    A: Analysis<'mir, 'ctx>,
{
    analysis: A,
    results: AnalysisStates<A::Domain>,
    gr: &'mir mir::Graph,
    ctx: &'mir Context<'ctx>,
    /// The next set of blocks to be analyzed
    working_set: HashSet<BlockId>,
}

impl<'mir, 'ctx, A> DataflowRunner<'mir, 'ctx, A>
where
    A: Analysis<'mir, 'ctx>,
{
    fn new(analysis: A, gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        let bot = A::Domain::bottom(gr, ctx);
        // FIXME this is doing a lot of extra work to fill in these "default"
        // values. Maybe we should use either a `Store<BlockId,
        // Option<A::Domain>>` or a `HashMap<BlockId, A::Domain>`, or somehow
        // guarantee that we walk the blocks in index-order.
        let entry_states = std::iter::repeat(bot.clone())
            .take(gr.blocks.len())
            .collect();
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
    fn run_inner(&mut self, block: BlockId) {
        let mut state = self.results.entry_states[block].clone();
        let block = &self.gr.blocks[block];
        self.propagate(&mut state, &block);

        // Compute the successor blocks and do any extra block-kind-dependent work.
        let successors = match &block.kind {
            BlockKind::Goto(blk) => std::slice::from_ref(blk),
            BlockKind::Switch { cond: _, blks } => blks,
            BlockKind::Ret => {
                self.results.exit_state = self.results.exit_state.join(&state);
                &[]
            }
            BlockKind::Call { blk, .. } => std::slice::from_ref(blk),
        };

        // If the propagated state differs from that of any successor, enter it
        // into the working set.
        for succ in successors {
            let prev_succ_state = &mut self.results.entry_states[*succ];
            let succ_state = prev_succ_state.join(&state);
            if &succ_state != prev_succ_state {
                *prev_succ_state = succ_state;
                self.working_set.insert(*succ);
            }
        }
    }

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

/// An execution environment for a simple analysis that makes only a single pass
/// over all blocks, regardless of the graph topology, and that only needs to
/// track a single (therefore non-block-local) instance of the analysis state.
/// The motivating example is the generation of a call graph.
pub struct SummaryRunner<'mir, 'ctx, A>
where
    A: Analysis<'mir, 'ctx>,
{
    analysis: A,
    gr: &'mir mir::Graph,
    ctx: &'mir Context<'ctx>,
}

// NOTE that we might eventually want `SummaryRunner` and `DataflowRunner` to
// implement some common trait.
impl<'mir, 'ctx, A> SummaryRunner<'mir, 'ctx, A>
where
    A: Analysis<'mir, 'ctx>,
{
    pub fn new(analysis: A, gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        Self { analysis, gr, ctx }
    }

    pub fn run(self) -> A::Domain {
        let mut state = A::Domain::bottom(self.gr, self.ctx);
        for block in self.gr.blocks.iter() {
            self.propagate(&mut state, block);
        }
        state
    }

    // FIXME this is (or should be) identical to the method of `DataflowRunner`
    // of the same name. Until this is abstracted by some common trait, this is
    // a possible point of failure if they get out of sync.
    fn propagate(&self, state: &mut A::Domain, block: &BasicBlock) {
        for stmt in block.stmts.iter() {
            self.analysis.trans_stmt(state, stmt, &block.data);
        }
        self.analysis.trans_block(state, &block.kind, &block.data);
    }
}
