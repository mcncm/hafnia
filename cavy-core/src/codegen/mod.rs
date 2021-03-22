//! This module implements the compiler backend.

use std::collections::HashMap;

use crate::{alloc::QubitAllocator, circuit::LirGraph, context::Context};
use crate::{
    ast::{FnId, UnOpKind},
    types::Type,
};
use crate::{circuit::Gate, mir::*};
use crate::{
    circuit::{Circuit, Qubit},
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
}

impl<'mir, 'ctx> LirBuilder<'mir, 'ctx> {
    fn new(gr: &'mir Graph, ctx: &'mir Context<'ctx>) -> Self {
        Self { gr, ctx }
    }

    fn build(mut self) -> LirGraph {
        let mut lir = LirGraph {
            args: 0,
            ancillae: 0,
            instructions: Vec::new(),
        };

        lir
    }
}

//    fn gen_function(&mut self, fn_id: FnId) {
//        use RvalueKind::*;
//
//        let gr = &self.mir.graphs[fn_id];
//        for stmt in gr.blocks[gr.entry_block].stmts.iter() {
//            let Stmt { place, rhs } = stmt;
//            match rhs.data {
//                BinOp(_, _, _) => {}
//                UnOp(UnOpKind::Minus, _right) => {}
//                RvalueKind::UnOp(UnOpKind::Not, right) => {
//                    let ty = &self.ctx.types[gr.locals[right].ty];
//                    match ty {
//                        Type::Bool => {
//                            // TODO classical case
//                        }
//                        Type::Q_Bool => {
//                            let qb = self.bindings.remove(&right).unwrap();
//                            let qb_idx = qb[0];
//                            self.circ.push(Gate::X(qb_idx));
//                            self.bindings.insert(*place, qb);
//                        }
//                        _ => unreachable!(),
//                    }
//                }
//                UnOp(UnOpKind::Linear, _right) => {
//                    let qb = self.alloc.q_bool().unwrap();
//                    // let qb_idx = qb[0];
//                    self.bindings.insert(*place, qb);
//                    // self.circ.push(crate::circuit::Gate::X(qb_idx));
//                    //
//                    // TODO determine the value of `right`, if it has a
//                    // determinable compile-time value, and apply a gate
//                    // appropriately.
//                }
//                UnOp(UnOpKind::Delin, _right) => {}
//                Const(_) => {
//                    // TODO
//                }
//                Copy(_) => {
//                    // TODO
//                }
//                Move(orig) => {
//                    self.bindings
//                        .insert(*place, self.bindings.get(&orig).unwrap().to_vec());
//                }
//            }
//        }
//    }
