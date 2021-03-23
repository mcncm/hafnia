//! This module implements the compiler backend.

use std::collections::{HashMap, HashSet};

use crate::{
    alloc::QubitAllocator,
    ast::BinOpKind,
    circuit::{Instruction, LirGraph},
    context::Context,
    mir,
};
use crate::{
    ast::{FnId, UnOpKind},
    types::Type,
};
use crate::{circuit::Gate, mir::*};
use crate::{
    circuit::{Circuit, VirtAddr},
    mir::Mir,
};

pub fn codegen(mir: &Mir, ctx: &Context) -> Circuit {
    let builder = CircuitBuilder::new(mir, ctx);
    builder.build()
}

struct CircuitBuilder<'mir, 'ctx> {
    ctx: &'mir Context<'ctx>,
    mir: &'mir Mir,
    circ: Circuit,
    /// Qubit allocator
    alloc: QubitAllocator,
}

impl<'mir, 'ctx> CircuitBuilder<'mir, 'ctx> {
    fn new(mir: &'mir Mir, ctx: &'mir Context<'ctx>) -> Self {
        // Missing entry point caught by previous analysis
        let entry_point = mir.entry_point.unwrap();
        let circ = Circuit {
            entry_point,
            graphs: HashMap::new(),
        };
        let alloc = QubitAllocator::new(ctx.conf.arch);
        Self {
            ctx,
            mir,
            circ,
            alloc,
        }
    }

    fn build(mut self) -> Circuit {
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
}

impl<'mir, 'ctx> LirBuilder<'mir, 'ctx> {
    fn new(gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        let lir = LirGraph {
            args: 0,
            ancillae: 0,
            instructions: Vec::new(),
        };
        Self { gr, ctx, lir }
    }

    fn build(mut self) -> LirGraph {
        self.translate_block(self.gr.entry_block);
        self.lir
    }

    /// Lower from the MIR, building from a given blck.
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
        let mir::Stmt { ref place, ref rhs } = stmt;
        match rhs.data {
            BinOp(_, _, _) => {}
            UnOp(op, right) => {}
            Use(_) => {}
        }
    }

    fn translate_switch(&mut self, cond: &LocalId, blks: &[BlockId]) {
        // FIXME This is incorrect, since of course no controls are applied. I
        // think, as we flesh this out, we should get the conditions on each
        // block from the analysis phase.
        for blk in blks {
            self.translate_block(*blk);
        }
    }

    fn translate_call(&mut self, callee: FnId, args: &Vec<LocalId>, blk: BlockId) {
        let args = args
            .iter()
            .map(|local| self.lookup_addr(local))
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
    fn lookup_addr(&self, local: &LocalId) -> Vec<VirtAddr> {
        todo!();
    }
}
