mod compute;
mod gates;
mod mem;

use mem::BitArray;

use smallvec::{smallvec, SmallVec};

use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet, VecDeque},
    iter::FromIterator,
    ops::RangeFrom,
    rc::Rc,
};

use crate::{
    circuit::{BaseGateQ, CircuitBuf, GateQ},
    context::Context,
    mir::*,
    session::Config,
    store::Store,
    types::TyId,
};

use self::mem::{AsBits, BitAllocators};

pub struct Environment<'a> {
    /// The graph locals. We must hold onto these here in order to have access
    /// to type information and be able look up bit addresses
    locals: &'a LocalStore,
    // NOTE: address lookups can probably be sped up considerably by modifying,
    // or removing, this data structure.
    /// Mapping of locals to memory locations. Note that they are _not_
    /// write-once, because of the SWAP-elimination optimization.
    bindings: Store<LocalId, EnvEntry<'a>>,
    /// Also needs a local `ctx` copy for type lookup
    ctx: &'a Context<'a>,
}

impl<'a> Environment<'a> {
    fn new(locals: &'a LocalStore, ctx: &'a Context<'a>) -> Self {
        let bindings = locals.iter().map(|loc| EnvEntry {
            bits: BitArray::uninit(loc.ty.size(ctx)),
            // It's *never* the callee's responsibility to destroy its
            // arguments; they're either owned, or they outlive the function.
            destructor: None,
        });
        Self {
            locals,
            bindings: Store::from_iter(bindings),
            ctx,
        }
    }

    fn type_of(&self, place: &Place) -> TyId {
        self.locals.type_of(place, self.ctx)
    }
}

/// Data tracked at a `LocalId`: the bits it points to, as well as any satellite
/// data associated with deferred analyses
struct EnvEntry<'a> {
    /// The memory bits this local points to
    bits: BitArray,
    destructor: Option<Rc<Destructor<'a>>>,
}

/// The destructor for a local which, in this first "toy" version, is just a
/// reference-counted blob in a DAG. The relatively naive--and ridiculously
/// heavyweight--way this creature works is a large part of what makes this
/// backend so "dynamic". Using these things is *approximately* writing Python.
///
/// NOTE: The assumption that they do form a DAG is not unconditional. We may
/// have to forbid recursion, for example.
///
/// NOTE: This works because of the order in which Rust runs `drop`s: first the
/// type's destructor, then those of its fields.
pub struct Destructor<'a> {
    parents: SmallVec<[Rc<Destructor<'a>>; 2]>,
    gates: Vec<BaseGateQ>,
    /// This will hold a shared mutable reference to the assembler, so it can
    /// freely unwind on drop.
    circ: Rc<RefCell<CircAssembler<'a>>>,
}

impl<'a> Destructor<'a> {
    fn new(circ: &Rc<RefCell<CircAssembler<'a>>>) -> Self {
        Self {
            parents: smallvec![],
            gates: Vec::new(),
            circ: circ.clone(),
        }
    }

    fn from_parents(parents: &[&Place], interp: &Interpreter<'a>) -> Self {
        let parents = parents
            .iter()
            .map(|parent| {
                interp.st.env.bindings[parent.root]
                    .destructor
                    .as_ref()
                    .map(|dest| dest.clone())
            })
            .flatten()
            .collect();
        Self {
            parents,
            gates: Vec::new(),
            circ: interp.circ.clone(),
        }
    }

    fn from_parent(parent: &Place, interp: &Interpreter<'a>) -> Self {
        Self::from_parents(&[parent], interp)
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
    circ: Rc<RefCell<CircAssembler<'a>>>,
    ctx: &'a Context<'a>,
}

impl<'a> Interpreter<'a> {
    pub fn new(mir: &'a Mir, ctx: &'a Context<'a>) -> Self {
        let entry_point = mir.entry_point.unwrap();
        let gr = &mir.graphs[entry_point];
        Self {
            circ: Rc::new(RefCell::new(CircAssembler::new(ctx))),
            st: InterpreterState::new(gr, ctx),
            ctx,
            mir,
        }
    }

    /// Run the interpreter, starting from its entry block.
    pub fn exec(mut self) -> CircuitBuf {
        self.run();
        let circ = match Rc::try_unwrap(self.circ) {
            Ok(refcell) => refcell.into_inner(),
            Err(_) => panic!("leftover pointer to circuit assembler"),
        };
        circ.gate_buf
    }

    fn funcall(&mut self, call: &FnCall) {
        let FnCall {
            callee, args, ret, ..
        } = call;
        let gr = &self.mir.graphs[*callee];
        let mut st = InterpreterState::new(gr, self.ctx);

        // Calling convention:

        let mut locals = st.env.locals.idx_enumerate();
        let (ret_local, _) = locals.next().unwrap();
        // Copy the return location
        let ret_adrs = ret.as_bits(&self.st.env);
        st.env.memcpy(&ret_local.into(), &ret_adrs);
        for (arg, (arg_local, _)) in args.iter().zip(locals) {
            let arg = match arg {
                Operand::Const(_) => unreachable!(),
                Operand::Copy(place) | Operand::Move(place) => place,
            };
            // Copy the argument locations
            let arg_adrs = arg.as_bits(&self.st.env);
            st.env.memcpy(&arg_local.into(), &arg_adrs);
        }

        // New stack frame
        std::mem::swap(&mut self.st, &mut st);
        self.run();
        // Restore interpreter state
        std::mem::swap(&mut self.st, &mut st);
        // // Copy return value back
        // self.st.env.mem_copy(ret, &ret_local);
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
            StmtKind::Drop(place) => self.exec_drop(place),
            StmtKind::Io(io) => {
                self.circ.borrow_mut().push_io(io, &self.st);
            }
            StmtKind::Nop => {}
        }
    }

    fn exec_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        self.compute_assn(place, rvalue);
    }

    // NOTE: [correctness] currently, only entire variables can drop, so for now
    // we don't have to worry about attempting to drop a containee and
    // destroying its container.
    fn exec_drop(&mut self, place: &Place) {
        self.compute_drop(place);
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
            BlockKind::Switch(switch) => {
                self.switch(&switch.cond, &switch.blks);
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
