use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use crate::{cavy_errors::ErrorBuf, mir, store::Store};
use crate::{context::Context, mir::*};

/// Marker type for forward-flowing dataflow analyses
pub struct Forward;

pub trait Lattice: Clone + PartialEq + Eq {
    fn join(&self, other: &Self) -> Self;

    fn bottom(gr: &Graph, ctx: &Context) -> Self;
}

/// Trait for a general dataflow analysis
pub trait Analysis<'mir, 'ctx> {
    type Direction;
    type Domain: Lattice;

    /// Apply the transfer function for a single statement
    fn trans_stmt(&self, state: &mut Self::Domain, stmt: &mir::Stmt);

    fn into_runner(self, ctx: &'mir Context<'ctx>, gr: &'mir Graph) -> Runner<'mir, 'ctx, Self>
    where
        Self: Sized,
    {
        Runner::new(self, gr, ctx)
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

/// An execution environment for an analysis
///
/// NOTE Can we do this with a *single* pass per direction? Can we do it without
/// generics? Probably only if we store the results in the analysis types
/// themselves.
pub struct Runner<'mir, 'ctx, A>
where
    A: Analysis<'mir, 'ctx>,
{
    analysis: A,
    results: AnalysisStates<A::Domain>,
    gr: &'mir mir::Graph,
    ctx: &'mir Context<'ctx>,
}

impl<'mir, 'ctx, A> Runner<'mir, 'ctx, A>
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
        Self {
            analysis,
            results,
            gr,
            ctx,
        }
    }

    pub fn run(mut self) -> AnalysisStates<A::Domain> {
        let state = A::Domain::bottom(self.gr, self.ctx);
        self.run_inner(state, &self.gr.entry_block);
        self.results
    }

    fn run_inner(&mut self, state: A::Domain, block: &BlockId) {
        let block = &self.gr.blocks[*block];
        let result = self.trans_block(state, &block);

        // FIXME this implementation is totally broken, of course: it will never
        // terminate if there are loops!
        match &block.kind {
            BlockKind::Goto(blk) => {
                self.results.entry_states[*blk] = result.clone();
                self.run_inner(result, blk);
            }
            BlockKind::Switch { .. } => {
                // for blk in blks.iter() {
                //     self.results.entry_states[*blk] = result.clone();
                //     self.run_inner(result, blk);
                // }
            }
            BlockKind::Ret => {
                self.results.exit_state = self.results.exit_state.join(&result);
            }
            BlockKind::Call { callee, args, blk } => todo!(),
        };
    }

    /// Apply the transfer function of a block, which is just the composition of
    /// the transfer functions of its statements. Begin with the state-on-entry,
    /// set the result value to this state, and mutate the state through the block.
    fn trans_block(&mut self, mut state: A::Domain, block: &BasicBlock) -> A::Domain {
        for stmt in block.stmts.iter() {
            self.analysis.trans_stmt(&mut state, stmt);
        }
        state
    }
}
