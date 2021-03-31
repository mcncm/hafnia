//! This module implements the compiler backend.

use std::collections::{HashMap, HashSet};

use crate::{
    ast::BinOpKind,
    ast::{FnId, UnOpKind},
    circuit::{Instruction, LirGraph, VirtAddr},
    context::Context,
    mir,
    store::Counter,
    types::{TyId, Type},
};
use crate::{circuit::Gate, mir::*};
use crate::{circuit::Lir, mir::Mir};

pub fn codegen(mir: &Mir, ctx: &Context) -> Lir {
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

#[derive(Clone)]
struct Allocation {
    qbits: Vec<usize>,
    cbits: Vec<usize>,
}

struct LirBuilder<'mir, 'ctx> {
    gr: &'mir Graph,
    ctx: &'mir Context<'ctx>,
    lir: LirGraph,
    bindings: HashMap<LocalId, Allocation>,
    qcounter: std::ops::RangeFrom<usize>,
    ccounter: std::ops::RangeFrom<usize>,
}

impl<'mir, 'ctx> LirBuilder<'mir, 'ctx> {
    fn new(gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        let lir = LirGraph {
            args: 0,
            ancillae: 0,
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

    /// Is this the right return type? It might be unnecessarily expensive to
    /// store these ranges of consecutive numbers.
    fn qalloc(&mut self, n: usize) -> Vec<usize> {
        // FIXME Ok, why does't this work with just `self.counter`?
        (&mut self.qcounter).take(n).collect()
    }

    /// FIXME regrettable name; has nothing to do with C `calloc`
    fn calloc(&mut self, n: usize) -> Vec<usize> {
        (&mut self.ccounter).take(n).collect()
    }

    /// Allocate space for a given type
    fn alloc_for(&mut self, ty: TyId) -> Allocation {
        let sz = ty.size(self.ctx);
        Allocation {
            qbits: self.qalloc(sz.qsize),
            cbits: self.qalloc(sz.csize),
        }
    }

    /// Create the initial local bindings for arguments and return site
    ///
    /// NOTE this method, along with the binding mechanism, is destined for
    /// replacement.
    fn bind_args(&mut self) {
        // Take one for each argument, plus one for the return site
        let n = self.gr.nargs + 1;
        for (idx, Local { ty, .. }) in self.gr.locals.idx_enumerate().take(n) {
            let allocation = self.alloc_for(*ty);
            self.bindings.insert(idx, allocation);
        }
    }

    /// Lower from the MIR, building from a given block.
    fn translate_block(&mut self, blk: BlockId) {
        let blk = &self.gr.blocks[blk];
        for stmt in blk.stmts.iter() {
            self.translate_stmt(stmt);
        }
        match &blk.kind {
            BlockKind::Goto(blk) => self.translate_block(*blk),
            BlockKind::Switch { cond, blks } => self.translate_switch(cond, blks),
            BlockKind::Call {
                callee,
                span: _,
                args,
                blk,
            } => {
                self.translate_call(*callee, args, *blk);
            }
            BlockKind::Ret => {}
        }
    }

    fn translate_stmt(&mut self, stmt: &mir::Stmt) {
        use RvalueKind::*;
        let (lplace, rhs) = match &stmt.kind {
            mir::StmtKind::Assn(place, rhs) => (place.clone(), rhs),
            _ => return,
        };

        let ty = self.gr.type_of(&lplace, self.ctx);
        match &rhs.data {
            BinOp(_op, _left, _right) => todo!(),
            UnOp(op, right) => {
                match op {
                    UnOpKind::Minus => todo!(),
                    UnOpKind::Not => {
                        // FIXME very much under construction
                        let right = match right {
                            Operand::Const(_) => unreachable!(),
                            Operand::Copy(x) => x,
                            Operand::Move(x) => x,
                        };
                        let bits = self.bindings.get(&right.root).unwrap().clone();
                        for bit in &bits.qbits {
                            let inst = Instruction::Gate(Gate::X(*bit));
                            self.lir.instructions.push(inst);
                        }
                        self.bindings.insert(lplace.root, bits);
                    }
                    UnOpKind::Linear => {
                        let allocation = self.alloc_for(ty);
                        self.bindings.insert(lplace.root, allocation);
                    }
                    UnOpKind::Delin => {
                        let allocation = self.alloc_for(ty);
                        self.bindings.insert(lplace.root, allocation);
                    }
                }
                // do some extra stuff
            }
            Use(val) => match val {
                Operand::Const(_) => {}
                Operand::Copy(rplace) | Operand::Move(rplace) => {
                    // FIXME This is currently failing integration test
                    // `return_assigned`, but that's probably ok.
                    let bits = self.bindings.get(&rplace.root).unwrap().clone();
                    self.bindings.insert(lplace.root, bits);
                }
            },
        }
    }

    fn translate_switch(&mut self, _cond: &Place, blks: &[BlockId]) {
        // FIXME This is incorrect, since of course no controls are applied. I
        // think, as we flesh this out, we should get the conditions on each
        // block from the analysis phase.
        for blk in blks {
            self.translate_block(*blk);
        }
    }

    fn translate_call(&mut self, callee: FnId, args: &[Operand], blk: BlockId) {
        let args = args
            .iter()
            .map(|arg| self.translate_arg(arg))
            .flatten()
            .collect();
        self.lir
            .instructions
            .push(Instruction::FnCall(callee, args));
        self.translate_block(blk);
    }

    /// are, we would need to supply a location (or more!) as well.
    /// Get the procedure-local virtual bit addresses associated with a local.
    ///
    /// NOTE: this doesn't work if addresses are position-dependent. If
    /// reassignment does the 'pre-optimization' of address reassignment, then
    /// we would need to keep track of that information. We might be able to
    /// avoid such a need by using SSA.
    fn translate_arg(&self, _arg: &Operand) -> Vec<VirtAddr> {
        todo!();
    }
}
