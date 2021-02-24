//! An analysis pass to detect the use of classical feedback. This
//! implementation isn't *fully* correct, since, like const evaluation, it must
//! be interprocedural.
//!
//! But we can prove whether, if the inputs to a function are not measurement
//! results, there is no classical feedback within a procedure.

use std::collections::{hash_map::Entry, HashMap};

use super::common::{Analysis, Forward, Lattice};
use crate::{
    ast::UnOpKind,
    mir::{BlockData, BlockKind, LocalId, RvalueKind},
    source::Span,
};

/// Tracks which local variables are downstream of a delinearization operator.
/// This works by conservatively propagating a provenance `Span` for values
/// downstream of a measurement result. If we linearize anyhting, we insert that
/// local and the appropriate `Span` into `lin`. We can then simply check if we
/// anythin in `lin` is also in `delin`.
///
/// Could be more efficiently packed into a bit vector.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct MeasState {
    /// This map points to the site a value's ancestor was measured
    pub delin: HashMap<LocalId, Span>,
    /// This map points to where values are linearized
    pub lin: HashMap<LocalId, Span>,
}

impl Lattice for MeasState {
    fn join(&self, other: &Self) -> Self {
        let mut delin = self.delin.clone();
        delin.extend(&other.delin);

        let mut lin = self.lin.clone();
        lin.extend(&other.lin);

        Self { delin, lin }
    }

    fn bottom(_: &crate::mir::Graph, _: &crate::context::Context) -> Self {
        Self {
            delin: HashMap::new(),
            lin: HashMap::new(),
        }
    }
}

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure. (...That must be what this
/// gen-kill thing is all about.)
pub struct FeedbackAnalysis {}

impl Analysis<'_, '_> for FeedbackAnalysis {
    type Direction = Forward;
    type Domain = MeasState;

    fn trans_stmt(&self, state: &mut Self::Domain, stmt: &crate::mir::Stmt, _data: &BlockData) {
        match &stmt.rhs.data {
            RvalueKind::BinOp(_, left, right) => {
                if let Some(&span) = state.delin.get(left).or_else(|| state.delin.get(right)) {
                    state.delin.insert(stmt.place, span);
                }
            }
            RvalueKind::UnOp(UnOpKind::Linear, right) => {
                state.lin.insert(*right, stmt.rhs.span);
            }
            RvalueKind::UnOp(UnOpKind::Delin, _) => {
                state.delin.insert(stmt.place, stmt.rhs.span);
            }
            RvalueKind::UnOp(_, right) => {
                if let Some(&span) = state.delin.get(right) {
                    state.delin.insert(stmt.place, span);
                }
            }
            RvalueKind::Const(_) => {}
            RvalueKind::Copy(local) | RvalueKind::Move(local) => {
                if let Some(&span) = state.delin.get(local) {
                    state.delin.insert(stmt.place, span);
                }
            }
        }
    }

    // TODO
    fn trans_block(&self, _state: &mut Self::Domain, _block: &BlockKind, _data: &BlockData) {}
}
