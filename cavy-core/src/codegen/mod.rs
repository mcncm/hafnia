//! This module implements the compiler backend.

use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    ops,
};

use crate::{
    ast::BinOpKind,
    ast::{FnId, UnOpKind},
    circuit::{BitSet, BitSetSlice, BitSetSliceMut, Gate, Instruction, Lir, LirGraph, VirtAddr},
    context::{Context, SymbolId},
    mir::{self, *},
    store::Counter,
    types::{TyId, Type},
};

pub fn translate(mir: &Mir, ctx: &Context) -> Lir {
    let builder = CircuitBuilder::new(mir, ctx);
    builder.build()
}

struct CircuitBuilder<'mir, 'ctx> {
    ctx: &'mir Context<'ctx>,
    mir: &'mir Mir,
    circ: Lir,
}

impl<'mir, 'ctx> CircuitBuilder<'mir, 'ctx> {
    fn new(mir: &'mir Mir, ctx: &'mir Context<'ctx>) -> Self {
        // Missing entry point caught by previous analysis
        //
        // FIXME: [BUG] Invariant not upheld. Missing main function is not
        // caught earlier.
        let entry_point = mir.entry_point.unwrap();
        let circ = Lir {
            entry_point,
            graphs: HashMap::new(),
        };
        Self { ctx, mir, circ }
    }

    fn build(mut self) -> Lir {
        for (fn_id, gr) in self.mir.graphs.idx_enumerate() {
            let lir = LirBuilder::new(gr, self.ctx).build();
            self.circ.graphs.insert(fn_id, lir);
        }
        self.circ
    }
}

struct LirBuilder<'mir, 'ctx> {
    gr: &'mir Graph,
    ctx: &'mir Context<'ctx>,
    lir: LirGraph,
    bindings: HashMap<LocalId, BitSet>,
    qcounter: ops::RangeFrom<usize>,
    ccounter: ops::RangeFrom<usize>,
}

impl<'mir, 'ctx> LirBuilder<'mir, 'ctx> {
    fn new(gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        let lir = LirGraph {
            qlocals: 0,
            clocals: 0,
            freed: Vec::new(),
            instructions: Vec::new(),
        };
        let bindings = HashMap::new();
        Self {
            gr,
            ctx,
            lir,
            bindings,
            qcounter: 0..,
            ccounter: 0..,
        }
    }

    fn build(mut self) -> LirGraph {
        self.bind_args();
        self.translate_block(self.gr.entry_block);
        self.lir
    }

    fn push_gate(&mut self, gate: Gate) {
        let inst = Instruction::Gate(gate);
        self.lir.instructions.push(inst);
    }
    /// Is this the right return type? It might be unnecessarily expensive to
    /// store these ranges of consecutive numbers.
    fn qalloc(&mut self, n: usize) -> Vec<usize> {
        // FIXME Ok, why does't this work with just `self.counter`?
        self.lir.qlocals += n;
        (&mut self.qcounter).take(n).collect()
    }

    /// FIXME regrettable name; has nothing to do with C `calloc`
    fn calloc(&mut self, n: usize) -> Vec<usize> {
        self.lir.clocals += n;
        (&mut self.ccounter).take(n).collect()
    }

    /// Allocate space for a given type
    fn alloc_for_ty(&mut self, ty: TyId) -> BitSet {
        let sz = ty.size(self.ctx);
        BitSet {
            qbits: self.qalloc(sz.qsize),
            cbits: self.calloc(sz.csize),
        }
    }

    /// Allocate space for a given place
    fn alloc_for(&mut self, place: &Place) -> BitSet {
        let ty = self.gr.type_of(&place, self.ctx);
        self.alloc_for_ty(ty)
    }

    /// Create a set of uninitialized pointers sized for the given type
    fn uninit_for_ty(&mut self, ty: TyId) -> BitSet {
        let sz = ty.size(self.ctx);
        BitSet::uninit(sz)
    }

    fn bitset_ranges(&self, place: &Place) -> (ops::Range<VirtAddr>, ops::Range<VirtAddr>) {
        // start with the root type
        let mut ty = self.gr.locals[place.root].ty;
        // traverse the allocation
        let (mut qi, mut ci) = (0, 0);
        for elem in &place.path {
            // TODO: [PERF] `ty.slot` should really return a `Slot` that also
            // contains an offset (and size?). These could be computed *once* when
            // the type is interned. This sort of "data about types" shouldn't
            // be computed *here*, of all place, and certainly not on every
            // call. In practice, it probably won't matter much, but it's really
            // bad in principle.
            for i in 0..*elem {
                // Actually, there's even more work being done here, because
                // `ty` is looked up repeatedly on *each* call to `slot`. There
                // are a *ton* of hashes going on here.
                let ty = ty.slot(i, self.ctx);
                let sz = ty.size(self.ctx);
                qi += sz.qsize;
                ci += sz.csize;
            }
            ty = ty.slot(*elem, self.ctx);
        }
        use crate::context::CtxDisplay;
        let sz = ty.size(self.ctx);
        let (qf, cf) = (qi + sz.qsize, ci + sz.csize);

        (qi..qf, ci..cf)
    }

    /// Get a sub-allocation at a place.
    fn bitset_at(&self, place: &Place) -> BitSetSlice {
        let ranges = self.bitset_ranges(place);
        let bitset = self.bindings.get(&place.root).unwrap();
        bitset.index(ranges)
    }

    fn insert_bindings(&mut self, place: &Place, bits: BitSet) {
        // TODO: [PERF] Can this be done without a double (or triple) lookup?
        if !self.bindings.contains_key(&place.root) {
            let ty = self.gr.locals[place.root].ty;
            let allocation = self.uninit_for_ty(ty);
            self.bindings.insert(place.root, allocation);
        }

        let ranges = self.bitset_ranges(&place);
        let lbits = self
            .bindings
            .get_mut(&place.root)
            .unwrap()
            .index_mut(ranges);
        lbits.qbits.copy_from_slice(&bits.qbits);
        lbits.cbits.copy_from_slice(&bits.cbits);
    }

    /// Create the initial local bindings for arguments and return site
    ///
    /// NOTE this method, along with the binding mechanism, is destined for
    /// replacement.
    fn bind_args(&mut self) {
        // Take one for each argument, plus one for the return site
        let n = self.gr.nargs + 1;
        for (idx, Local { ty, .. }) in self.gr.locals.idx_enumerate().take(n) {
            let allocation = self.alloc_for_ty(*ty);
            self.bindings.insert(idx, allocation);
        }
    }

    /// Lower from the MIR, building from a given block.
    fn translate_block(&mut self, blk: BlockId) {
        let blk = &self.gr[blk];
        for stmt in blk.stmts.iter() {
            self.translate_stmt(stmt);
        }
        match &blk.kind {
            BlockKind::Goto(blk) => self.translate_block(*blk),
            BlockKind::Switch { cond, blks } => self.translate_switch(cond, blks),
            BlockKind::Call(call) => {
                self.translate_call(call.callee, &call.args, &call.ret, call.blk);
            }
            BlockKind::Ret => {}
        }
    }

    fn translate_stmt(&mut self, stmt: &mir::Stmt) {
        use RvalueKind::*;
        let (lplace, rhs) = match &stmt.kind {
            mir::StmtKind::Assn(place, rhs) => (place.clone(), rhs),
            mir::StmtKind::Io(io) => {
                self.translate_io(io);
                return;
            }
            mir::StmtKind::Assert(_place) => {
                todo!();
            }
            _ => return,
        };

        match &rhs.data {
            BinOp(_op, _left, _right) => todo!(),

            UnOp(UnOpKind::Minus, _) => todo!(),

            UnOp(UnOpKind::Not, right) => {
                // FIXME very much under construction
                let right = match right {
                    Operand::Const(_) => unreachable!(),
                    Operand::Copy(x) => x,
                    Operand::Move(x) => x,
                };
                let bits = self.bitset_at(right).to_owned();
                for addr in &bits.qbits {
                    self.push_gate(Gate::X(*addr));
                }
                self.insert_bindings(&lplace, bits);
            }

            UnOp(UnOpKind::Split, right) => {
                // FIXME very much under construction
                // Also, copy of the `Not` case
                let right = match right {
                    Operand::Const(_) => unreachable!(),
                    Operand::Copy(x) => x,
                    Operand::Move(x) => x,
                };
                let bits = self.bitset_at(right).to_owned();
                for addr in &bits.qbits {
                    self.push_gate(Gate::H(*addr));
                }
                self.insert_bindings(&lplace, bits);
            }

            UnOp(UnOpKind::Linear, right) => {
                let allocation = self.alloc_for(&lplace);
                match right {
                    Operand::Const(value) => {
                        for (i, b) in value.bits().iter().enumerate() {
                            if *b {
                                let addr = allocation.qbits[i];
                                self.push_gate(Gate::X(addr));
                            }
                        }
                    }
                    Operand::Copy(_) => {
                        unimplemented!("Classical feedback not yet implemented")
                    }
                    Operand::Move(_) => {
                        unimplemented!("Classical feedback not yet implemented")
                    }
                }
                self.insert_bindings(&lplace, allocation);
            }

            UnOp(UnOpKind::Delin, right) => {
                let rplace = match right {
                    Operand::Const(_) => unreachable!(),
                    Operand::Copy(_) => unreachable!(),
                    Operand::Move(place) => place,
                };
                let lbits = self.alloc_for(&lplace);
                let rbits = self.bitset_at(&rplace).to_owned();

                debug_assert_eq!(rbits.cbits.len(), 0);
                debug_assert_eq!(lbits.qbits.len(), 0);
                debug_assert_eq!(lbits.cbits.len(), rbits.qbits.len());

                for (_lbit, rbit) in lbits.cbits.iter().zip(rbits.qbits.iter()) {
                    self.push_gate(Gate::M(*rbit));
                }

                self.insert_bindings(&lplace, lbits);
            }

            Use(val) => match val {
                Operand::Const(_val) => {
                    // TODO: [IMPL] Add the gates to set an initial value for
                    // classical bits
                    let allocation = self.alloc_for(&lplace);
                    self.insert_bindings(&lplace, allocation);
                }
                Operand::Copy(rplace) | Operand::Move(rplace) => {
                    //  FIXME [TESTFAIL: return_assigned] This is currently
                    //  failing an integration test but that's probably ok.
                    // `to_owned` maybe, unfortunately, necessary
                    let rbits = self.bitset_at(rplace).to_owned();
                    self.insert_bindings(&lplace, rbits);
                }
            },
            Ref(_, _) => todo!(),
        }
    }

    fn translate_io(&mut self, io: &IoStmtKind) {
        match io {
            IoStmtKind::In => {}
            IoStmtKind::Out { place, symb } => {
                let bits = self.bitset_at(place).to_owned();

                // We should only be able to return purely classical types to
                // the host computer.
                debug_assert!(bits.qbits.len() == 0);

                for (elem, &addr) in bits.cbits.iter().enumerate() {
                    // NOTE Maybe this should keep propagating `SymbolId`s (this
                    // is a very unfortunate clone inside a loop), but the
                    // `target` API can't currently handle them, as it doesn't
                    // have access to the context. Now is not the time to change
                    // that.
                    let gate = crate::circuit::IoOutGate {
                        name: self.ctx.symbols[*symb].clone(),
                        addr,
                        elem,
                    };
                    self.push_gate(Gate::Out(Box::new(gate)));
                }
                return;
            }
        }
    }

    fn translate_switch(&mut self, _cond: &Place, blks: &[BlockId]) {
        // FIXME This is incorrect, since of course no controls are applied. I
        // think, as we flesh this out, we should get the conditions on each
        // block from the analysis phase.
        //
        // Counterargument: we might also not! The block structure can very well
        // change due to optimizations.
        for blk in blks {
            self.translate_block(*blk);
        }
    }

    fn translate_call(&mut self, callee: FnId, args: &[Operand], ret: &Place, blk: BlockId) {
        // FIXME we shouldn't always rebind this!
        let ret_local = &self.gr.locals[ret.root];
        let allocation = self.alloc_for_ty(ret_local.ty);
        self.bindings.insert(ret.root, allocation);
        // At the Lir level, there's no such thing as a return value. The return
        // place is simply the first argument.
        let args = std::iter::once(self.bitset_at(ret).to_owned())
            .chain(args.iter().map(|arg| self.translate_arg(arg)))
            .fold(BitSet::new(), |mut acc, mut b| {
                acc.append(&mut b);
                acc
            });
        self.lir
            .instructions
            .push(Instruction::FnCall(callee, args));
        self.translate_block(blk);
    }

    // NOTE: this doesn't work if addresses are position-dependent. If
    // reassignment does the 'pre-optimization' of address reassignment, then
    // we would need to keep track of that information. We might be able to
    // avoid such a need by using SSA.
    //
    // TODO: for now we're _not_ going to pass-through constants. Instead,
    // before passing a constant, we will allocate new bits for it, and hand
    // those off to the function call. This is a pretty major compromise, but
    // now I have a deadline and I'm making compromises.
    fn translate_arg(&mut self, arg: &Operand) -> BitSet {
        use Operand::*;
        match arg {
            Const(value) => {
                // Get a new allocation corresponding to this value's size.
                //
                // TODO: When quantum types are allowed to be const, this
                // allocation will become more complicated: we'll actually need
                // to know the precise type of the value.
                let allocation = BitSet {
                    qbits: vec![],
                    cbits: self.calloc(value.size()),
                };

                // generate code to assign the value in that allocation
                let _bits = value.bits();
                // TODO

                allocation
            }
            Copy(place) | Move(place) => self.bitset_at(place).to_owned(),
        }
    }
}
