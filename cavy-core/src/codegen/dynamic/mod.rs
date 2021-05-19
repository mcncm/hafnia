mod compute;
mod gates;
mod mem;
mod uncompute_pts;
mod util;

use mem::BitArray;

use smallvec::{smallvec, SmallVec};

use std::{
    cell::{Ref, RefCell},
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    iter::FromIterator,
    ops::RangeFrom,
    rc::Rc,
};

use crate::{
    analysis::controls::{ControlPlaces, CtrlCond},
    ast::FnId,
    circuit::{BaseGateQ, CircuitBuf, GateQ, Qbit},
    context::Context,
    mir::*,
    place_tree::{PlaceNode, PlaceStore},
    session::Config,
    store::Store,
    types::TyId,
};

use self::{
    mem::{AsBits, BitAllocators},
    uncompute_pts::{cfg_facts, CfgFacts},
};

/// Main entry point for this module
pub fn translate(mir: &Mir, ctx: &Context) -> CircuitBuf {
    let mir_facts: Store<FnId, CfgFacts> = mir.graphs.iter().map(|gr| cfg_facts(gr, ctx)).collect();

    let interp = Interpreter::new(mir, &mir_facts, ctx);
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
///
/// Maybe partition the immutable-for-a-stack-frame ones from the always-mutable
/// ones?
pub struct InterpreterState<'a> {
    // "immutable" fields
    ctx: &'a Context<'a>,
    /// The forward graph
    blocks: &'a BlockStore,
    /// The predecessor graph
    preds: Ref<'a, Store<BlockId, Vec<BlockId>>>,
    /// Locals: needed to retrieve types
    locals: &'a LocalStore,
    /// Stack memory addresses for each local
    bindings: Store<LocalId, BitArray>,
    /// The controls on each block
    controls: &'a ControlPlaces,
    /// The points at which destructors must run
    uncompute_pts: &'a BTreeMap<GraphPt, Vec<LocalId>>,

    // stateful fields
    /// Destructors from inactive blocks, to be merged later. (TODO doesn't work for loops)
    latent_destructors: HashMap<BlockId, PlaceStore<Rc<Destructor<'a>>>>,
    /// The active forest of destructors
    destructors: PlaceStore<Rc<Destructor<'a>>>,
    /// The currently active block
    blk: BlockId,
    /// Blocks that will not get executed again (TODO this doesn't work for loops)
    visited_blocks: HashSet<BlockId>,
}

impl<'a> InterpreterState<'a> {
    fn new(gr: &'a Graph, cfg_facts: &'a CfgFacts, ctx: &'a Context<'a>) -> Self {
        Self {
            blocks: gr.get_blocks(),
            preds: gr.get_preds(),
            visited_blocks: HashSet::new(),
            ctx,
            locals: &gr.locals,
            blk: gr.entry_block,
            latent_destructors: HashMap::new(),
            controls: &cfg_facts.controls,
            uncompute_pts: &cfg_facts.uncompute_pts,
            bindings: Store::new(),
            destructors: PlaceStore::new(gr.locals.len()),
        }
    }

    fn type_of(&self, place: &Place) -> TyId {
        self.locals.type_of(place, self.ctx)
    }

    fn ctrls(&self) -> &[CtrlCond] {
        &self.controls[self.blk]
    }

    fn save_destructors(&mut self, blk: BlockId) {
        self.latent_destructors
            .insert(blk, self.destructors.clone());
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
    controls: Vec<(Qbit, bool)>,
}

impl<'a> CircAssembler<'a> {
    fn new(ctx: &'a Context<'a>) -> Self {
        Self {
            ctx,
            allocators: BitAllocators::new(),
            gate_buf: CircuitBuf::new(),
            controls: vec![],
        }
    }
}

pub struct Interpreter<'a> {
    mir: &'a Mir,
    st: InterpreterState<'a>,
    circ: Rc<RefCell<CircAssembler<'a>>>,
    mir_facts: &'a Store<FnId, CfgFacts>,
    ctx: &'a Context<'a>,
}

impl<'a> Interpreter<'a> {
    pub fn new(mir: &'a Mir, mir_facts: &'a Store<FnId, CfgFacts>, ctx: &'a Context<'a>) -> Self {
        let entry_point = mir.entry_point.unwrap();
        let gr = &mir.graphs[entry_point];
        let cfg_facts = &mir_facts[entry_point];
        let mut st = InterpreterState::new(gr, cfg_facts, ctx);
        let circ = Rc::new(RefCell::new(CircAssembler::new(ctx)));

        // Initialize the environment
        st.mem_init(
            std::iter::empty(),
            &mut circ.borrow_mut().allocators,
            &mir_facts[entry_point].shared_mem_borrows,
        );
        Self {
            ctx,
            circ,
            st,
            mir,
            mir_facts,
        }
    }

    /// Run the interpreter, starting from its entry block.
    pub fn exec(mut self) -> CircuitBuf {
        self.run();

        // FIXME: some destructors are never run because they’re executed when
        // their lifetimes *end*. But some lifetimes are *empty*. We could just
        // never compute any reference with an empty lifetime. They could be
        // optimized away, in fact. But to make our lives simpler, we'll run
        // a "gc pass" where we eliminate all remaining destructors.
        self.st.destructors = PlaceStore::new(0);

        let circ = match Rc::try_unwrap(self.circ) {
            Ok(refcell) => refcell.into_inner(),
            Err(_) => {
                dbg!(self.st.destructors);
                panic!("dangling pointer to circuit assembler")
            }
        };
        circ.gate_buf
    }

    fn funcall(&mut self, call: &FnCall) {
        let FnCall {
            callee, args, ret, ..
        } = call;
        let gr = &self.mir.graphs[*callee];
        let cfg_facts = &self.mir_facts[*callee];
        let mut st = InterpreterState::new(gr, cfg_facts, self.ctx);

        // Calling conventions
        let caller_ret_adr = ret.as_bits(&self.st);
        let caller_arg_adrs = args.iter().map(|caller_arg| {
            let caller_arg = match caller_arg {
                Operand::Const(_) => unreachable!(),
                Operand::Copy(place) | Operand::Move(place) => place,
            };
            caller_arg.as_bits(&self.st)
        });
        // Copy the parameter locations
        let params = std::iter::once(caller_ret_adr).chain(caller_arg_adrs);
        st.mem_init(
            params,
            &mut self.circ.borrow_mut().allocators,
            &self.mir_facts[*callee].shared_mem_borrows,
        );

        // New stack frame
        std::mem::swap(&mut self.st, &mut st);
        self.run();

        // Accept destructor for return value and restore interpreter state
        let mut ret_dest = st.destructors.get_node_mut(ret);
        ret_dest.replace(
            &mut self
                .st
                .destructors
                .get_root_mut(Graph::return_site())
                .clone(),
        );
        std::mem::swap(&mut self.st, &mut st);
    }

    fn switch(&mut self, _cond: &Place, _blks: &[BlockId]) {}

    pub fn run(&mut self) {
        self.exec_block(self.st.blk);
    }

    fn exec_block(&mut self, blk: BlockId) {
        let block = &self.st.blocks[blk];
        self.st.blk = blk;

        // controls
        let mut controls = vec![];
        for CtrlCond { place, value } in self.st.ctrls() {
            // assert!(value); // they should all be positive...?
            let ctrl_addrs = place.as_bits(&self.st);
            for bit in ctrl_addrs.qbits.iter() {
                controls.push((*bit, *value));
            }
        }

        let mut circ = self.circ.borrow_mut();
        circ.controls = controls;
        drop(circ);

        for (loc, stmt) in block.stmts.iter().enumerate() {
            self.uncompute(GraphPt { blk, stmt: loc });
            self.exec_stmt(stmt);
        }
        self.st.visited_blocks.insert(blk);
        self.terminate(&block.kind);
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
            // self.st.save_destructors(*succ);
            if self.dfs_eligible(*succ) {
                self.exec_block(*succ);
            }
        }
    }
}

// === boilerplate impls ===

impl<'a> std::fmt::Debug for Destructor<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "gates: {:?}", self.gates)?;
        f.write_str("parents:\n")?;
        for parent in self.parents.iter() {
            writeln!(f, "\t {:?}", parent)?;
        }
        Ok(())
    }
}
