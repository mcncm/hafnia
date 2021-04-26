mod compute;
mod gates;
mod mem;

use mem::BitAllocator;

use std::{
    cell::Ref,
    collections::{HashSet, VecDeque},
    ops::RangeFrom,
};

use crate::{
    circuit::{Circuit, Gate},
    context::Context,
    mir::*,
    session::Config,
    store::Store,
};

pub struct Environment<'a> {
    /// The graph locals. We must hold onto these here in order to have access
    /// to type information and be able look up bit addresses
    locals: &'a LocalStore,
    /// Also needs a local `ctx` copy for type lookup
    ctx: &'a Context<'a>,
}

impl<'a> Environment<'a> {
    fn new(locals: &'a LocalStore, ctx: &'a Context<'a>) -> Self {
        Self { locals, ctx }
    }

    fn insert(&mut self, _place: &Place, _value: ()) {
        todo!()
    }

    fn get(&self, _place: &LocalId) -> &EnvEntry {
        todo!()
    }
}

/// This struct essentially represents a stack frame. Everything that is pushed
/// onto the stack when a new procedure is called should live here.
pub struct InterpreterState<'a> {
    /// The forward graph
    blocks: &'a BlockStore,
    /// The predecessor graph
    preds: Ref<'a, Store<BlockId, Vec<BlockId>>>,
    /// Blocks that could get executed next
    next_candidates: Vec<BlockId>,
    /// Blocks that will not get executed again (TODO this won't work for loops)
    visited_blocks: HashSet<BlockId>,
    /// Program state in this scope
    env: Environment<'a>,
}

impl<'a> InterpreterState<'a> {
    fn new(gr: &'a Graph, ctx: &'a Context<'a>) -> Self {
        Self {
            blocks: gr.get_blocks(),
            preds: gr.get_preds(),
            env: Environment::new(&gr.locals, ctx),
            next_candidates: vec![gr.entry_block],
            visited_blocks: HashSet::new(),
        }
    }
}

/// Data tracked at a `LocalId`: the bits it points to, as well as any satellite
/// data associated with deferred analyses
struct EnvEntry {
    bits: mem::BitSet,
}

struct CircAssembler<'a> {
    /// This needs to own the allocater because we might use temporaries while
    /// inserting gates.
    alloc: BitAllocator<'a>,
    gate_buf: Circuit,
}

impl<'a> CircAssembler<'a> {
    fn new(ctx: &'a Context<'a>) -> Self {
        Self {
            alloc: BitAllocator::new(ctx),
            gate_buf: Circuit::new(),
        }
    }
}

pub struct Interpreter<'a> {
    mir: &'a Mir,
    st: InterpreterState<'a>,
    circ: CircAssembler<'a>,
    ctx: &'a Context<'a>,
}

impl<'a> Interpreter<'a> {
    fn new(mir: &'a Mir, ctx: &'a Context<'a>) -> Self {
        let entry_point = mir.entry_point.unwrap();
        let gr = &mir.graphs[entry_point];
        Self {
            circ: CircAssembler::new(ctx),
            st: InterpreterState::new(gr, ctx),
            ctx,
            mir,
        }
    }

    /// Run the interpreter, starting from its entry block.
    fn exec(mut self) -> Circuit {
        let mut block_candidates = vec![];
        while !block_candidates.is_empty() {
            std::mem::swap(&mut block_candidates, &mut self.st.next_candidates);
            for blk in block_candidates.drain(0..) {
                self.exec_block(blk);
            }
        }
        self.circ.gate_buf
    }

    fn exec_block(&mut self, blk_id: BlockId) {
        let blk = &self.st.blocks[blk_id];
        for stmt in &blk.stmts {
            self.exec_stmt(stmt);
        }
        self.st.visited_blocks.insert(blk_id);
        self.terminate(&blk.kind);
    }

    fn exec_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Assn(place, rvalue) => self.exec_assn(&place, &rvalue),
            StmtKind::Assert(_place) => {
                // See, this is why we need these analysis things. It's really
                // pretty hard to say whether something has been asserted from
                // local data alone, if you have any join points.
                todo!();
            }
            StmtKind::Io(_io) => {
                todo!();
            }
            StmtKind::Nop => {}
        }
    }

    fn exec_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        let value = self.compute(rvalue);
        self.st.env.insert(place, value);
    }

    /// Checks if a block is eligible according to the DFS traversal criterion:
    /// all of its predecessors should have been visited.
    fn dfs_eligible(&self, blk: BlockId) -> bool {
        self.st.preds[blk]
            .iter()
            .all(|pred| self.st.visited_blocks.contains(pred))
    }

    /// After finishing with a block, we might have to do a procedure call or
    /// add more blocks to the candidates list
    fn terminate(&mut self, kind: &BlockKind) {
        // TODO: procedure calls: figure out calling convention
        // TODO: conditionals: add some conditions, I guess
        for succ in kind.successors() {
            if self.dfs_eligible(*succ) {
                self.exec_block(*succ);
            }
        }
    }
}
