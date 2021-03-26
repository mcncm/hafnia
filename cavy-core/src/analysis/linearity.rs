use std::collections::{hash_map::Entry, HashMap};

use super::common::{Analysis, Forward, Lattice};
use crate::{
    mir::{self, BlockData, BlockKind, LocalId, Operand, RvalueKind},
    source::Span,
};

/// Counts how many times a local has been moved.
///
/// NOTE Could use some kind of bit vector for this; it would save a lot of
/// space and time.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct MoveState {
    /// This map points to the location of the first move of each local that is
    /// not currently live.
    pub moved: HashMap<LocalId, Span>,
    /// This map points to the second move, if any, of each local
    pub double_moved: HashMap<LocalId, (Span, Span)>,
}

impl Lattice for MoveState {
    fn join(&self, other: &Self) -> Self {
        // We choose to extend a copy of the hashmap, overwriting `Span`s that
        // might be in there. That's ok: if we're merging from two paths, we
        // only care if at least one of them has moved something.
        //
        // Note as above, the clone might be too expensive.
        let mut moved = self.moved.clone();
        moved.extend(&other.moved);

        let mut double_moved = self.double_moved.clone();
        double_moved.extend(&other.double_moved);

        Self {
            moved,
            double_moved,
        }
    }

    fn bottom(_: &mir::Graph, _: &crate::context::Context) -> Self {
        Self {
            moved: HashMap::new(),
            double_moved: HashMap::new(),
        }
    }
}

impl MoveState {
    /// Update the move state with a new operand use, adding anything linear to
    /// the moved list.
    fn move_from(&mut self, arg: &Operand, span: Span) {
        if let Operand::Move(local) = arg {
            match self.moved.entry(*local) {
                Entry::Occupied(entry) => {
                    let fst_move = *entry.get();
                    self.double_moved.insert(*local, (fst_move, span));
                }
                Entry::Vacant(entry) => {
                    entry.insert(span);
                }
            }
        }
    }

    /// Update a variable into which a value has been moved by taking it off the
    /// moved list.
    fn move_into(&mut self, place: &LocalId) {
        self.moved.remove(place);
    }
}

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure.
pub struct LinearityAnalysis {}

impl LinearityAnalysis {}

impl Analysis<'_, '_> for LinearityAnalysis {
    type Direction = Forward;
    type Domain = MoveState;

    fn trans_stmt(&self, state: &mut Self::Domain, stmt: &mir::Stmt, _data: &BlockData) {
        // NOTE this pattern is repeated in a lot of these analyses. Consider an
        // abstraction.
        let (place, rhs) = match &stmt.kind {
            mir::StmtKind::Assn(place, rhs) => (*place, rhs),
            _ => return,
        };

        match &rhs.data {
            RvalueKind::BinOp(_, left, right) => {
                // FIXME There should really be more fine-grained span data here
                state.move_from(left, rhs.span);
                state.move_from(right, rhs.span);
            }
            RvalueKind::UnOp(_, right) => state.move_from(right, rhs.span),
            RvalueKind::Use(arg) => state.move_from(arg, rhs.span),
        }
        state.move_into(&place);
    }

    fn trans_block(&self, _state: &mut Self::Domain, _block: &BlockKind, _data: &BlockData) {
        // TODO
    }
}
