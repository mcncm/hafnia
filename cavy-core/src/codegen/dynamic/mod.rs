mod compute;
mod gates;
mod mem;
mod util;

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
    place_tree::{PlaceNode, PlaceStore},
    session::Config,
    store::Store,
    types::TyId,
};

use self::mem::{AsBits, BitAllocators};

/// Main entry point for this module
pub fn translate(mir: &Mir, ctx: &Context) -> CircuitBuf {
    let interp = Interpreter::new(mir, ctx);
    interp.exec()
}

/// The destructor for a local which, in this first "toy" version, is just a
/// reference-counted blob in a DAG. The relatively naive--and ridiculously
/// heavyweight--way this creature works is a large part of what makes this
/// backend so "dynamic". Using these things is *approximately* writing Python.
///
/// NOTE: The assumption that they do form a DAG is not unconditional. This just
/// won't work with recursion, for example.
///
/// NOTE: This works because of the order in which Rust runs `drop`s: first the
/// type's destructor, then those of its fields.
pub struct Destructor<'a> {
    parents: SmallVec<[Rc<Destructor<'a>>; 2]>,
    /// The gates to unwind on drop. Classical uncomputation not yet supported.
    gates: Vec<GateQ>,
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
            .map(|parent| interp.st.destructors.get(parent).map(|dest| dest.clone()))
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

/// This struct essentially represents a stack frame: everything respecting a
/// stack discipline that is pushed for a new procedure call.
///
/// Even though this struct is a bit of a stopgap for this "demo" backend, I'm
/// not happy with it. It's weird that mingles data that lives for the duration
/// of a stack frame with "environment"-like state that changes from statement
/// to statement.
pub struct InterpreterState<'a> {
    // immutable fields
    ctx: &'a Context<'a>,
    /// The forward graph
    blocks: &'a BlockStore,
    /// The predecessor graph
    preds: Ref<'a, Store<BlockId, Vec<BlockId>>>,
    /// Locals: needed to retrieve types
    locals: &'a LocalStore,
    /// Stack memory addresses for each local
    bindings: Store<LocalId, BitArray>,
    // stateful fields
    /// The forest of destructors
    destructors: PlaceStore<Rc<Destructor<'a>>>,
    /// Blocks that could get executed next
    next_candidates: Vec<BlockId>,
    /// Blocks that will not get executed again (TODO this won't work for loops)
    visited_blocks: HashSet<BlockId>,
}

impl<'a> InterpreterState<'a> {
    fn new(gr: &'a Graph, ctx: &'a Context<'a>) -> Self {
        Self {
            blocks: gr.get_blocks(),
            preds: gr.get_preds(),
            next_candidates: vec![gr.entry_block],
            visited_blocks: HashSet::new(),
            ctx,
            locals: &gr.locals,
            bindings: Store::new(),
            destructors: PlaceStore::new(gr.locals.len()),
        }
    }

    fn type_of(&self, place: &Place) -> TyId {
        self.locals.type_of(place, self.ctx)
    }
}

struct CircAssembler<'a> {
    // NOTE: I'm no longer sure that this comment is true. I think that we can
    // statically allocate everything, including temporaries used when
    // inserting/expanding gates.
    //
    // But, for now, there is probably no *harm* in leaving this ownership
    // relationship as-is. We can evolve it later.
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
        let mut st = InterpreterState::new(gr, ctx);
        let circ = Rc::new(RefCell::new(CircAssembler::new(ctx)));

        // Initialize the environment
        st.mem_init(std::iter::empty(), &mut circ.borrow_mut().allocators);
        Self { ctx, circ, st, mir }
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

        // Calling conventions
        let caller_ret_adr = ret.as_bits(&self.st);
        let caller_arg_adrs = args.iter().map(|caller_arg| {
            let caller_arg = match caller_arg {
                Operand::Const(_) => unreachable!(),
                Operand::Copy(place) | Operand::Move(place) => place,
            };
            caller_arg.as_bits(&self.st)
        });
        // Copy the parameters locations
        let params = std::iter::once(caller_ret_adr).chain(caller_arg_adrs);
        st.mem_init(params, &mut self.circ.borrow_mut().allocators);

        // New stack frame
        std::mem::swap(&mut self.st, &mut st);
        self.run();
        // Restore interpreter state
        std::mem::swap(&mut self.st, &mut st);
    }

    fn switch(&mut self, cond: &Place, _blks: &[BlockId]) {
        let cond_bits = self.st.bits_at(cond);
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
