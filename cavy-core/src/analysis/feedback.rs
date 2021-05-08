//! An analysis pass to detect the use of classical feedback. This
//! implementation isn't *fully* correct, since, like const evaluation, it must
//! be interprocedural.
//!
//! But we can prove whether, if the inputs to a function are not measurement
//! results, there is no classical feedback within a procedure.

use std::collections::{hash_map::Entry, HashMap};

use super::dataflow::{DataflowAnalysis, Forward, Lattice, Statementwise};
use crate::{
    ast::UnOpKind,
    mir::{self, BlockId, BlockKind, GraphPt, LocalId, Operand, Place, RvalueKind},
    source::Span,
};

/// Tracks which local variables are downstream of a delinearization operator.
/// This works by conservatively propagating a provenance `Span` for values
/// downstream of a measurement result. If we linearize anyhting, we insert that
/// local and the appropriate `Span` into `lin`. We can then simply check if we
/// anythin in `lin` is also in `delin`.
///
/// Could be more efficiently packed into a bit vector.
#[derive(Default, PartialEq, Eq, Clone, Debug)]
pub struct MeasState {
    /// This map points to the site a value's ancestor was measured
    pub delin: HashMap<LocalId, Span>,
    /// This map points to where values are linearized
    pub lin: HashMap<LocalId, Span>,
}

impl Lattice for MeasState {
    fn join(self, other: Self) -> Self {
        let delin = self.delin.join(other.delin);
        let lin = self.lin.join(other.lin);
        Self { delin, lin }
    }
}

impl MeasState {
    /// Get a measurement upstream of an operand, if we care about it; that is,
    /// if the operand is `Copy`.
    fn upstream_delin(&self, arg: &Operand) -> Option<&Span> {
        if let Operand::Copy(place) = arg {
            // FIXME
            self.delin.get(&place.root)
        } else {
            None
        }
    }
}

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure. (...That must be what this
/// gen-kill thing is all about.)
pub struct FeedbackAnalysis {}

impl DataflowAnalysis<Forward, Statementwise> for FeedbackAnalysis {
    type Domain = MeasState;

    fn bottom(&self) -> Self::Domain {
        Self::Domain::default()
    }

    fn transfer_stmt(&self, state: &mut Self::Domain, stmt: &mir::Stmt, _loc: GraphPt) {
        use RvalueKind::*;
        let (place, rhs) = match &stmt.kind {
            mir::StmtKind::Assn(place, rhs) => (place.clone(), rhs),
            _ => return,
        };

        match &rhs.data {
            BinOp(_, left, right) => {
                if let Some(&span) = state
                    .upstream_delin(left)
                    .or_else(|| state.upstream_delin(right))
                {
                    state.delin.insert(place.root, span);
                }
            }
            UnOp(UnOpKind::Linear, Operand::Copy(right))
            | UnOp(UnOpKind::Linear, Operand::Move(right)) => {
                // FIXME
                state.lin.insert(right.root, rhs.span);
            }
            UnOp(UnOpKind::Delin, _) => {
                state.delin.insert(place.root, rhs.span);
            }
            UnOp(_, operand) | Use(operand) => {
                if let Some(&span) = state.upstream_delin(operand) {
                    state.delin.insert(place.root, span);
                }
            }
            // I *think* refs should do nothing here! They are merely taking a
            // reference, not actually "doing" anything
            Ref(_, _) => {}
        }
    }

    // TODO
    fn transfer_block(&self, _state: &mut Self::Domain, _block: &BlockKind, _pt: GraphPt) {}

    fn initial_state(&self, _blk: BlockId) -> Self::Domain {
        Self::Domain::default()
    }
}
