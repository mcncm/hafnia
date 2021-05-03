//! This will be the classic live-variables analysis, but with a statement-level
//! granularity, as required by the subsequent borrow-checking analyses.
//!
//! From the NLL RFC:
//!
//! "Traditional compiler compute liveness based on variables, but we wish to
//! compute liveness for lifetimes. We can extend a variable-based analysis to
//! lifetimes by saying that a lifetime L is live at a point P if there is some
//! variable p which is live at P, and L appears in the type of p."
//!
//! So, the first step for us is to compute variable liveness, and then extend
//! this to livetime/region liveness by generating constraints from the results.

use std::marker::PhantomData;

use crate::{context::Context, mir::*, store::BitSet};

use super::{
    super::dataflow::{Backward, DataflowAnalysis, Lattice, Statementwise},
    *,
};

use bitvec::prelude::*;

#[derive(Clone, PartialEq, Eq)]
pub struct LiveVars(BitSet<LocalId>);

// The canonical set lattice
impl Lattice for LiveVars {
    fn bottom(gr: &Graph, _ctx: &Context) -> Self {
        let blocks = gr.len();
        Self(BitSet::empty(blocks))
    }

    /// Simple set union
    fn join(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

pub struct LivenessAnalysis {
    /// The number of locals in the CFG
    vars: usize,
}

impl LivenessAnalysis {
    pub fn new(gr: &Graph) -> Self {
        Self {
            vars: gr.locals.len(),
        }
    }

    // Write to a variable
    fn kill(&self, state: &mut LiveVars, place: &Place) {
        state.0.set(place.root, false);
    }

    // NOTE: should we just detect multiple-use of linear variables *here*?
    //
    // Read from a variable
    fn gen(&self, state: &mut LiveVars, place: &Place) {
        state.0.set(place.root, true);
    }

    // NOTE: this method is the core of the liveness analysis. It's actually a
    // bit subtle, and I'm not completely sure that it's right. We'll iterate on
    // it.
    //
    // Read from a rhs
    fn gen_rvalue(&self, state: &mut LiveVars, rhs: &Rvalue) {
        use RvalueKind::*;
        match &rhs.data {
            RvalueKind::BinOp(_, fst, snd) => {
                self.gen_operand(state, fst);
                self.gen_operand(state, snd);
            }
            RvalueKind::UnOp(_, arg) => self.gen_operand(state, arg),
            RvalueKind::Ref(_, arg) => self.gen(state, arg),
            RvalueKind::Use(arg) => self.gen_operand(state, arg),
        }
    }

    fn gen_operand(&self, state: &mut LiveVars, operand: &Operand) {
        operand.place().map(|place| self.gen(state, place));
    }
}

impl DataflowAnalysis<Backward, Statementwise> for LivenessAnalysis {
    type Domain = LiveVars;

    fn transfer_block(&self, _state: &mut Self::Domain, _block: &BlockKind, _loc: BlockId) {}

    fn initial_state(&self, _blk: BlockId) -> Self::Domain {
        LiveVars(BitSet::empty(self.vars))
    }

    fn transfer_stmt(&self, state: &mut Self::Domain, stmt: &Stmt, _loc: GraphLoc) {
        match &stmt.kind {
            StmtKind::Assn(lhs, rhs) => {
                self.gen_rvalue(state, rhs);
                self.kill(state, lhs);
            }
            StmtKind::Assert(place) | StmtKind::Drop(place) => self.gen(state, place),
            StmtKind::Io(io) => match io {
                IoStmtKind::In => {}
                IoStmtKind::Out { place, .. } => self.gen(state, place),
            },
            StmtKind::Nop => {}
        }
    }
}
