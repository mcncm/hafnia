mod compute;
mod gates;
mod mem;

use mem::BitSet;

use std::{
    cell::Ref,
    collections::{HashMap, HashSet, VecDeque},
    iter::FromIterator,
    ops::RangeFrom,
};

use crate::{
    circuit::{CircuitBuf, GateQ},
    context::Context,
    mir::*,
    session::Config,
    store::Store,
};

use self::mem::BitAllocators;

pub struct Environment<'a> {
    /// The graph locals. We must hold onto these here in order to have access
    /// to type information and be able look up bit addresses
    locals: &'a LocalStore,
    // NOTE: address lookups can probably be sped up considerably by modifying,
    // or removing, this data structure.
    /// Mapping of locals to memory locations. Note that they are _not_
    /// write-once, because of the SWAP-elimination optimization.
    bindings: Store<LocalId, EnvEntry>,
    /// Also needs a local `ctx` copy for type lookup
    ctx: &'a Context<'a>,
}

impl<'a> Environment<'a> {
    fn new(locals: &'a LocalStore, ctx: &'a Context<'a>) -> Self {
        let bindings = locals.iter().map(|loc| EnvEntry {
            bits: BitSet::uninit(loc.ty.size(ctx)),
        });
        Self {
            locals,
            bindings: Store::from_iter(bindings),
            ctx,
        }
    }
}

/// Data tracked at a `LocalId`: the bits it points to, as well as any satellite
/// data associated with deferred analyses
struct EnvEntry {
    bits: BitSet,
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

struct CircAssembler<'a> {
    /// This needs to own the allocators because we might use temporaries while
    /// inserting gates.
    allocators: BitAllocators,
    /// ...And, like almost everything else, a copy of the Context.
    ctx: &'a Context<'a>,
    gate_buf: CircuitBuf,
}

impl<'a> CircAssembler<'a> {
    fn new(ctx: &'a Context<'a>) -> Self {
        Self {
            ctx,
            allocators: BitAllocators::new(),
            gate_buf: CircuitBuf::new(),
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
    pub fn new(mir: &'a Mir, ctx: &'a Context<'a>) -> Self {
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
    pub fn exec(mut self) -> CircuitBuf {
        self.run();
        self.circ.gate_buf
    }

    fn funcall(&mut self, call: &FnCall) {
        let FnCall {
            callee, args, ret, ..
        } = call;
        let gr = &self.mir.graphs[*callee];
        let mut st = InterpreterState::new(gr, self.ctx);
        // Copy local state
        let mut locals = st.env.locals.idx_enumerate();
        let (ret_local, _) = locals.next().unwrap();
        for (arg, (arg_local, _)) in args.iter().zip(locals) {
            let arg = match arg {
                Operand::Const(_) => unreachable!(),
                Operand::Copy(place) | Operand::Move(place) => place,
            };

            st.env.insert(&arg_local.into(), self.st.env.bits_at(&arg));
        }
        // New stack frame
        std::mem::swap(&mut self.st, &mut st);
        self.run();
        // Restore interpreter state
        std::mem::swap(&mut self.st, &mut st);
        // Copy return value back
        self.st.env.insert(ret, st.env.bits_at(&ret_local.into()));
    }

    fn switch(&mut self, cond: &Place, _blks: &[BlockId]) {
        let cond_bits = self.st.env.bits_at(cond);
        // No `match` statements yet; only `if`s.
        debug_assert!(cond_bits.qbits.len() + cond_bits.cbits.len() == 1);
        todo!()
    }

    pub fn run(&mut self) {
        let mut block_candidates = vec![];
        self.swap_blocks(&mut block_candidates);
        while !block_candidates.is_empty() {
            for blk in block_candidates.drain(0..) {
                self.exec_block(blk);
            }
            self.swap_blocks(&mut block_candidates);
        }
    }

    fn swap_blocks(&mut self, other: &mut Vec<BlockId>) {
        std::mem::swap(other, &mut self.st.next_candidates);
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
            StmtKind::Drop(place) => self.circ.push_drop(place, &self.st),
            StmtKind::Io(io) => {
                self.circ.push_io(io, &self.st);
            }
            StmtKind::Nop => {}
        }
    }

    fn exec_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        self.compute_assn(place, rvalue);
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
        match kind {
            BlockKind::Goto(_) => {}
            BlockKind::Switch { cond, blks } => {
                self.switch(cond, blks);
                return;
            }
            BlockKind::Call(call) => {
                self.funcall(call);
            }
            BlockKind::Ret => {
                return;
            }
        }
        // TODO: conditionals: add some conditions, I guess
        for succ in kind.successors() {
            if self.dfs_eligible(*succ) {
                self.exec_block(*succ);
            }
        }
    }
}
