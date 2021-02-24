use std::collections::{hash_map::Entry, HashMap};

use super::common::{Analysis, Forward, Lattice};
use crate::{
    mir::{BlockData, BlockKind, LocalId, RvalueKind},
    source::Span,
};

/// Counts how many times a local has been moved.
///
/// NOTE Could use some kind of bit vector for this; it would save a lot of
/// space and time.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct MoveState {
    /// This map points to the location of the first move of each local
    pub moved: HashMap<LocalId, Span>,
    /// This map points to the second move, if any, of each local
    pub double_moved: HashMap<LocalId, Span>,
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

    fn bottom(_: &crate::mir::Graph, _: &crate::context::Context) -> Self {
        Self {
            moved: HashMap::new(),
            double_moved: HashMap::new(),
        }
    }
}

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure.
pub struct LinearityAnalysis {}

impl Analysis<'_, '_> for LinearityAnalysis {
    type Direction = Forward;
    type Domain = MoveState;

    fn trans_stmt(&self, state: &mut Self::Domain, stmt: &crate::mir::Stmt, _data: &BlockData) {
        match &stmt.rhs.data {
            RvalueKind::BinOp(_, _, _) => {}
            RvalueKind::UnOp(_, _) => {}
            RvalueKind::Const(_) => {}
            RvalueKind::Copy(_) => {}
            RvalueKind::Move(local) => match state.moved.entry(*local) {
                Entry::Occupied(_) => {
                    state.double_moved.insert(*local, stmt.rhs.span);
                }
                Entry::Vacant(entry) => {
                    entry.insert(stmt.rhs.span);
                }
            },
        }
    }

    fn trans_block(&self, _state: &mut Self::Domain, _block: &BlockKind, _data: &BlockData) {
        // TODO
    }
}
