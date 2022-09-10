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
//!
//! NOTE: Constraint generation based on liveness doesn't appear here, but in
//! live_const.rs. They're conceptually linked, but I might want to move the
//! liveness dataflow analysis *up*, and make it available outside of region
//! inference and borrow checking.

use std::marker::PhantomData;

use crate::{
    analysis::controls::{ControlPlaces, CtrlCond},
    ast::IoDirection,
    bitset,
    context::Context,
    mir::*,
    store::BitSet,
};

use super::{
    super::dataflow::{Backward, DataflowAnalysis, Lattice, Statementwise},
    *,
};

bitset! { LiveVars(LocalId) }

// The canonical set lattice
impl Lattice for LiveVars {
    /// Simple set union
    fn join(self, other: Self) -> Self {
        self | other
    }
}

pub struct LivenessAnalysis<'a> {
    /// The number of locals in the CFG
    vars: usize,
    controls: &'a ControlPlaces,
}

impl<'a> LivenessAnalysis<'a> {
    pub fn new(gr: &'a Graph, controls: &'a ControlPlaces) -> Self {
        Self {
            vars: gr.locals.len(),
            controls,
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
            RvalueKind::Array(items) => {
                items.iter().for_each(|item| self.gen_operand(state, item));
            }
        }
    }

    fn gen_operand(&self, state: &mut LiveVars, operand: &Operand) {
        if let Some(place) = operand.place() {
            self.gen(state, place)
        }
    }

    /// This is a difference from Rust: controls have to be live for the
    /// entirety of all blocks they control, because this is a circuit model,
    /// and the data has to *be there* to attach control gates to.
    ///
    /// Incidentally, this one of the reasons a liveness analysis based on
    /// `Place`s--rather than variables--might be a lot better.
    fn gen_controls(&self, state: &mut LiveVars, pt: GraphPt) {
        for CtrlCond { place, .. } in &self.controls[pt.blk] {
            self.gen(state, place);
        }
    }
}

impl<'a> DataflowAnalysis<Backward, Statementwise> for LivenessAnalysis<'a> {
    type Domain = LiveVars;

    fn bottom(&self) -> Self::Domain {
        LiveVars::empty(self.vars)
    }

    fn transfer_block_post(&self, state: &mut Self::Domain, block: &BlockKind, pt: GraphPt) {
        match block {
            BlockKind::Goto(_) => {}
            BlockKind::Switch(switch) => self.gen(state, &switch.cond),
            BlockKind::Call(call) => {
                let FnCall {
                    ref args,
                    ref ret,
                    ref callee,
                    ..
                } = **call;
                // write to the return value
                self.kill(state, ret);
                // read from the args
                for arg in args.iter() {
                    self.gen_operand(state, arg);
                }
                // And then, what do we do with the function? At the moment this
                // doesn't matter, but it will.
                let _ = callee;
            }
            BlockKind::Ret => {
                // read from the return value
                self.gen(state, &Graph::return_site().into())
            }
        }
        // *should* only have to do this *once*, at the block tail
        //
        // TODO: ok, but is this "post" or "pre"? I can't keep straight my
        // convention for backwards analyses.
        self.gen_controls(state, pt);
    }

    fn initial_state(&self, _blk: BlockId) -> Self::Domain {
        LiveVars(BitSet::empty(self.vars))
    }

    fn transfer_stmt_post(&self, state: &mut Self::Domain, stmt: &Stmt, _loc: GraphPt) {
        match &stmt.kind {
            StmtKind::Assn(lhs, rhs) => {
                self.kill(state, lhs);
                self.gen_rvalue(state, rhs);
            }
            StmtKind::Assert(place) => self.gen(state, place),
            StmtKind::Drop(_place) => {
                // TODO: add `may_dangle` check to lifetimes?
                // For now, assume that all references can dangle.
            }
            StmtKind::Io(io) => match &io.dir {
                IoDirection::In => self.kill(state, &io.place),
                IoDirection::Out => self.gen(state, &io.place),
            },
            StmtKind::Nop => {}
        }
    }
}
