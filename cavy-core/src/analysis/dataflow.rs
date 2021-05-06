use std::{cell::Ref, collections::hash_map::Entry};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};
use std::{hash::Hash, ops};

use mir::Stmt;

use super::graph::{self, Postorder, Preorder};

use crate::{ast::FnId, context::Context, mir::*};
use crate::{cavy_errors::ErrorBuf, mir, store::Store};

/// The data we need available to perform dataflow analyses. This is just here
/// to package the `DataflowRunner` arguments. It's also a poor data structure
/// name.
pub struct DataflowCtx<'a> {
    pub ctx: &'a Context<'a>,
    /// The graph itself
    pub gr: &'a Graph,
    /// Some precomputed graph properties
    pub postorder: Postorder<BlockId>,
    pub preorder: Preorder<BlockId>,
    /// The length of each block in the graph
    pub block_sizes: Vec<usize>,
}

impl<'a> DataflowCtx<'a> {
    pub fn new(gr: &'a Graph, ctx: &'a Context) -> Self {
        let (pre, post) = graph::traversals(gr);
        let block_sizes = gr.iter().map(|block| block.len()).collect();
        Self {
            ctx,
            gr,
            postorder: post,
            preorder: pre,
            block_sizes,
        }
    }
}

/// Also quite a poor name: this is something that's able to supply a postorder
/// or preorder.
pub trait OrderProvider<D: Direction> {
    fn get_order(&self) -> &D::RevOrder;
}

impl<'a> OrderProvider<Forward> for DataflowCtx<'a> {
    fn get_order(&self) -> &Postorder<BlockId> {
        &self.postorder
    }
}

impl<'a> OrderProvider<Backward> for DataflowCtx<'a> {
    fn get_order(&self) -> &Preorder<BlockId> {
        &self.preorder
    }
}

pub trait Direction {
    /// The _reverse_ of the traversal order for an analysis in this direction,
    /// because we will be using our ordered list of blocks as a stack.
    type RevOrder: Clone + Into<Vec<BlockId>>;

    fn init_worklist(gr: &Graph) -> Vec<BlockId>;
}

/// Marker type for forward-flowing dataflow analyses
pub struct Forward;
impl Direction for Forward {
    type RevOrder = Postorder<BlockId>;

    fn init_worklist(gr: &Graph) -> Vec<BlockId> {
        // This probably isn't RPO. It's just *some* order, and the entry block
        // should be at the top of the stack. If I have time later, I'll go back
        // and compute the orders correctly and all that.
        //
        // This is also inefficient, does an extra allocation, etc.
        let mut blks: Vec<BlockId> = gr.idx_enumerate().map(|(blk, _)| blk).collect();
        blks.reverse();
        debug_assert_eq!(blks.last().unwrap(), &gr.entry_block);
        blks
    }
}

/// Marker type for backward-flowing dataflow analyses
pub struct Backward;
impl Direction for Backward {
    type RevOrder = Preorder<BlockId>;

    fn init_worklist(gr: &Graph) -> Vec<BlockId> {
        // Again, basically just *some* order. The exit block should be last.
        let blks: Vec<BlockId> = gr.idx_enumerate().map(|(blk, _)| blk).collect();
        debug_assert_eq!(blks.last().unwrap(), &gr.exit_block);
        blks
    }
}

/// Does an analysis measure state for blocks alone, or at the
/// statement-by-statement level?
pub trait Granularity {}

pub struct Blockwise;
impl Granularity for Blockwise {}

pub struct Statementwise;
impl Granularity for Statementwise {}

/// The main trait for analysis data, representing a join-semilattice.
pub trait Lattice: Clone + PartialEq + Eq {
    /// Some of these will really be "meets". Instead of actually distinguishing
    /// and abstracting over lattice orientation, I'll just reimplement a few
    /// things a bunch of times. Fine for now.
    fn join(self, other: Self) -> Self;

    fn bottom(gr: &Graph, ctx: &Context) -> Self;
}

/// Any set forms a join-semilattice under unions.
impl<T> Lattice for HashSet<T>
where
    T: Clone + Eq + Hash,
{
    fn bottom(_gr: &Graph, _ctx: &Context) -> Self {
        Self::new()
    }

    fn join(mut self, other: Self) -> Self {
        self.extend(other.into_iter());
        self
    }
}

impl<K, V> Lattice for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone + Eq,
{
    fn bottom(_gr: &Graph, _ctx: &Context) -> Self {
        Self::new()
    }

    fn join(mut self, other: Self) -> Self {
        self.extend(other.into_iter().map(|(k, v)| (k, v)));
        self
    }
}

/// Trait for a general dataflow analysis
pub trait DataflowAnalysis<D, G>
where
    D: Direction,
    G: Granularity,
{
    type Domain: Lattice;

    /// Apply the transfer function for a single statement. Empty default implementation
    fn transfer_stmt(&self, _state: &mut Self::Domain, _stmt: &Stmt, _loc: GraphPt) {}

    /// Apply the transfer function for the end of a basic block
    fn transfer_block(&self, state: &mut Self::Domain, block: &BlockKind, loc: BlockId);

    /// Compute state for the entry block
    fn initial_state(&self, blk: BlockId) -> Self::Domain;

    /// Transform predecessor blocks for joining
    fn propagate_predecessor(&self, _blk: BlockId, pred: &Self::Domain) -> Self::Domain {
        pred.clone()
    }

    /// A default inner implementation for `join_predecessors`. This is useful
    /// because of analyses like dominators, where we'd like to take ({n} |
    /// &_pred {dom(pred)}). This gives us maximum freedom to simply define
    /// `join_predecessors` to simply use the default behavior, plus flipping a
    /// single bit.
    fn join_predecessors_inner<'a, I: Iterator<Item = (BlockId, &'a Self::Domain)>>(
        &self,
        blk: BlockId,
        preds: I,
    ) -> Self::Domain
    where
        Self::Domain: 'a,
    {
        let mut preds = preds.map(|(blk, pred)| self.propagate_predecessor(blk, pred));
        if let Some(head) = preds.next() {
            preds.fold(head, |acc, pred| acc.join(pred))
        } else {
            self.initial_state(blk)
        }
    }

    /// Construct the state-on-entry to a block from the states of its predecessors
    fn join_predecessors<'a, I: Iterator<Item = (BlockId, &'a Self::Domain)>>(
        &self,
        blk: BlockId,
        preds: I,
    ) -> Self::Domain
    where
        Self::Domain: 'a,
    {
        self.join_predecessors_inner(blk, preds)
    }
}

/// Dataflow states for a block-granularity analysis
type BlockStates<L> = Store<mir::BlockId, L>;

/// Dataflow states for a statement-granularity analysis
type StmtStates<L> = Store<mir::BlockId, Vec<L>>;

/// An execution environment for a dataflow analysis, using the Killdall method.

/// Ok, this is the data structure we'll use to back our worklist. The
/// `BTreeMap::pop` API isn't stable yet, so we'll just use this. No idea if
/// it's faster in practice (or not) to add a `HashSet` for uniqueness. One of
/// those "asymptotically-faster-vs-in-practice-faster" questions.
struct UniqueStack<T: PartialEq + Eq> {
    stack: Vec<T>,
}

impl<T: PartialEq + Eq> UniqueStack<T> {
    fn push(&mut self, elem: T) {
        if !self.stack.contains(&elem) {
            self.stack.push(elem);
        }
    }

    fn pop(&mut self) -> Option<T> {
        self.stack.pop()
    }
}

impl<T: PartialEq + Eq> FromIterator<T> for UniqueStack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            stack: iter.into_iter().collect(),
        }
    }
}

pub struct DataflowRunner<'a, A, D, G>
where
    A: DataflowAnalysis<D, G>,
    D: Direction,
    G: Granularity,
{
    analysis: A,
    ctx: &'a Context<'a>,
    gr: &'a mir::Graph,
    preds: Ref<'a, Store<BlockId, Vec<BlockId>>>,
    /// Per-block analysis states, used for granularity `Blockwise`
    pub block_states: BlockStates<A::Domain>,
    /// Per-statement analysis states, used for granularity `Statementwise`
    pub stmt_states: StmtStates<A::Domain>,
    /// The next set of blocks to be analyzed, together with their new starting
    /// states
    worklist: UniqueStack<BlockId>,
}

impl<'a, A, D, G> DataflowRunner<'a, A, D, G>
where
    A: DataflowAnalysis<D, G>,
    D: Direction,
    G: Granularity,
    Self: Propagate<A, D, G>,
    DataflowCtx<'a>: OrderProvider<D>,
{
    // NOTE: This is starting to have a lot of arguments. I wonder if there's
    // something better we could do here. Certainly all of them will have the
    // graph and context in common; that's a start. But pretty code is not my
    // goal at this second. This will do for now.
    pub fn new(analysis: A, context: &DataflowCtx<'a>) -> Self {
        let gr = context.gr;
        let ctx = context.ctx;
        let preds = gr.get_preds();
        let rev_order = OrderProvider::<D>::get_order(context);
        let worklist = UniqueStack {
            stack: rev_order.clone().into(),
        };
        Self {
            analysis,
            block_states: Self::init_block_states(gr, ctx),
            stmt_states: Self::init_stmt_states(gr, ctx),
            gr,
            ctx,
            preds,
            worklist,
        }
    }

    /*
    NOTE: to self: do *not* try to make this method consume `self` and return a
    type generic over `G`. You've already wasted more time on it than it could
    possibly save you between now and your immediate deadline.
    */

    pub fn run(mut self) -> Self {
        while let Some(blk) = self.worklist.pop() {
            self.run_inner(blk);
        }
        self
    }

    /// Update the state associated with a single block. We'll take the previous
    /// entry state, propagate it, and compare the exit state to the entry
    /// states of any successor block. If they differ, they are updated and
    /// these blocks are entered into the working set. We'll also take any
    /// action associated with the block kind.
    fn run_inner(&mut self, blk: BlockId) {
        /*
        First, get the starting state for this block from the exit states of
        its parents.

        In the `Statementwise` case, we'll keep this generic over direction for
        now by using the `block_states` for something: we'll clone the *last*
        state in the block, whether at the top (first statement) or bottom
        (block tail), into the `block_states` entry for that block. This entails
        a little extra bookkeeping that must be synchronized, but it also means
        we aren't writing *still more* generics boilerplate to pick the "last"
        state from either the top or bottom of the block.
        */
        let preds = self.predecessors(blk);
        let pred_states = preds.iter().map(|&pred| (pred, &self.block_states[pred]));
        let mut state = self.analysis.join_predecessors(blk, pred_states);
        self.propagate(&mut state, blk);

        // NOTE: yes, this allocation is unnecessary. No, don't try to get rid of it
        // right now. Proving safety to the compiler is not worth it: it turns
        // into a generics mess.
        let succs = self.successors(blk).to_owned();

        // If the propagated state differs from that of any successor, enter it
        // into the working set.
        for succ in succs {
            self.worklist.push(succ);
        }
    }

    /// This doesn't need to be part of the `Update` trait, since it's the same
    /// for both granularities.
    fn init_block_states(gr: &Graph, ctx: &Context) -> BlockStates<A::Domain> {
        let bot = A::Domain::bottom(gr, ctx);
        std::iter::repeat(bot.clone()).take(gr.len()).collect()
    }

    /// This doesn't need to be part of the `Update` trait, since it's the same
    /// for both granularities.
    fn update_block_state(&mut self, blk: BlockId, state: &A::Domain) {
        self.block_states[blk] = state.clone();
    }
}

pub trait Propagate<A, D, G>
where
    A: DataflowAnalysis<D, G>,
    D: Direction,
    G: Granularity,
    Self: Update<A, D, G>,
{
    fn successors<'b>(&'b self, blk_id: BlockId) -> &'b [BlockId];

    fn predecessors<'b>(&'b self, blk_id: BlockId) -> &'b [BlockId];

    fn propagate(&mut self, state: &mut A::Domain, blk: BlockId);
}

impl<'a, A, G> Propagate<A, Forward, G> for DataflowRunner<'a, A, Forward, G>
where
    A: DataflowAnalysis<Forward, G>,
    G: Granularity,
    Self: Update<A, Forward, G>,
{
    fn successors(&self, blk_id: BlockId) -> &[BlockId] {
        let block = &self.gr[blk_id];
        block.successors()
    }

    fn predecessors(&self, blk_id: BlockId) -> &[BlockId] {
        &self.preds[blk_id]
    }

    /// Apply the transfer function of a block, which is just the composition of
    /// the transfer functions of its statements. Begin with the state-on-entry,
    /// set the result value to this state, and mutate the state through the block.
    fn propagate(&mut self, state: &mut A::Domain, blk: BlockId) {
        let block = &self.gr[blk];
        for (loc, stmt) in block.stmts.iter().enumerate() {
            let gl = GraphPt { blk, stmt: loc };
            self.analysis.transfer_stmt(state, stmt, gl);
            self.update_stmt_state(blk, loc, state);
        }
        self.analysis.transfer_block(state, &block.kind, blk);
        // Update the *block tail* state
        self.update_stmt_state(blk, block.stmts.len(), state);
        self.update_block_state(blk, state);
    }
}

impl<'a, A, G> Propagate<A, Backward, G> for DataflowRunner<'a, A, Backward, G>
where
    A: DataflowAnalysis<Backward, G>,
    G: Granularity,
    Self: Update<A, Backward, G>,
{
    fn successors(&self, blk_id: BlockId) -> &[BlockId] {
        &self.preds[blk_id]
    }

    fn predecessors(&self, blk_id: BlockId) -> &[BlockId] {
        let block = &self.gr[blk_id];
        block.successors()
    }

    /// Apply the transfer function of a block, which is just the composition of
    /// the transfer functions of its statements. Begin with the state-on-entry,
    /// set the result value to this state, and mutate the state through the block.
    fn propagate(&mut self, state: &mut A::Domain, blk: BlockId) {
        let block = &self.gr[blk];
        self.analysis.transfer_block(state, &block.kind, blk);
        // Update the *block tail* state
        self.update_stmt_state(blk, block.stmts.len(), state);
        for (loc, stmt) in block.stmts.iter().enumerate().rev() {
            let gl = GraphPt { blk, stmt: loc };
            self.analysis.transfer_stmt(state, stmt, gl);
            self.update_stmt_state(blk, loc, state);
        }
        // NOTE: keep this at the end! The `block_state` should be the *last*
        // state computed, whether at the top or bottom (`Backward` or `Forward`
        // case, resp.) of the block.
        self.update_block_state(blk, state);
    }
}

pub trait Update<A, D, G>
where
    A: DataflowAnalysis<D, G>,
    D: Direction,
    G: Granularity,
{
    /// Default implementation for `Blockwise` case
    fn init_stmt_states(_gr: &Graph, _ctx: &Context) -> StmtStates<A::Domain> {
        Store::new()
    }

    /// Default implementation for the `Blockwise` case: do nothing!
    fn update_stmt_state(&mut self, _blk: BlockId, _loc: usize, _state: &A::Domain) {}
}

/// For the statementwise case, we must override the default implementations for the statement methods
impl<'a, A, D> Update<A, D, Statementwise> for DataflowRunner<'a, A, D, Statementwise>
where
    A: DataflowAnalysis<D, Statementwise>,
    D: Direction,
{
    fn init_stmt_states(gr: &Graph, ctx: &Context) -> StmtStates<A::Domain> {
        let bot = A::Domain::bottom(gr, ctx);
        gr.iter()
            .map(|block| {
                // One state for each statement and one for the block tail
                let len = block.len();
                std::iter::repeat(bot.clone()).take(len).collect()
            })
            .collect()
    }

    fn update_stmt_state(&mut self, blk: BlockId, loc: usize, state: &A::Domain) {
        self.stmt_states[blk][loc] = state.clone();
    }
}

impl<'a, A, D> Update<A, D, Blockwise> for DataflowRunner<'a, A, D, Blockwise>
where
    A: DataflowAnalysis<D, Blockwise>,
    D: Direction,
{
    /// Can I make this call unnecessary? The `stmt_states` don't even need to
    /// be initialized for blockwise granularity.
    fn init_stmt_states(gr: &Graph, ctx: &Context) -> StmtStates<A::Domain> {
        let bot = A::Domain::bottom(gr, ctx);
        gr.iter()
            .map(|block| {
                let len = block.len();
                std::iter::repeat(bot.clone()).take(len).collect()
            })
            .collect()
    }
}

// == Summary analyses ==

/// A simple analysis that makes only a single pass over all blocks, *regardless
/// of the graph topology*, and that only needs to track a single (therefore
/// non-block-local) instance of the analysis state.
pub trait SummaryAnalysis {
    /// Apply the transfer function for a single statement
    fn trans_stmt(&mut self, stmt: &Stmt, loc: &GraphPt);

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
                let loc = GraphPt {
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

// === Some impls ===

// FIXME: for now, assume that *any* data of this shape is the result of a
// statement-granularity dataflow analysis. That's not a "true" assumption, but
// we can probably get away with it while we're hacking these modules out.
// Ideally, we should return some `DataflowResults<Granularity>` type, but this
// turns out to be surprisingly finicky.
impl<T> ops::Index<GraphPt> for Store<BlockId, Vec<T>> {
    type Output = T;

    fn index(&self, pt: GraphPt) -> &Self::Output {
        &self[pt.blk][pt.stmt]
    }
}

impl<T> ops::IndexMut<GraphPt> for Store<BlockId, Vec<T>> {
    fn index_mut(&mut self, pt: GraphPt) -> &mut Self::Output {
        &mut self[pt.blk][pt.stmt]
    }
}
