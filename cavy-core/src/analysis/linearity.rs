use std::collections::{hash_map::Entry, HashMap, HashSet};

use super::dataflow::{Blockwise, DataflowAnalysis, Forward, Lattice};
use crate::{mir::*, source::Span};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MoveKind {
    /// A field of this data was moved
    Partial,
    /// This whole object was moved
    Full,
}

/// A case of a variable being moved
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Move {
    pub kind: MoveKind,
    pub site: Span,
}

impl Move {
    fn full(site: Span) -> Self {
        Self {
            kind: MoveKind::Full,
            site,
        }
    }

    fn partial(site: Span) -> Self {
        Self {
            kind: MoveKind::Partial,
            site,
        }
    }
}

// This kind of pointer tree is going to be terrible for the cache. Should I
// replace it with a flat array?
/// The spans where a path and its fields have been (first) moved.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct MoveTree {
    /// Site of the first move
    mov: Option<Move>,
    /// Fields of the data
    fields: Vec<MoveTree>,
}

impl MoveTree {
    // TODO This requires searching the whole tree, probably making a bunch of
    // cache misses. These trees are small, so it's not the end of the world,
    // but do keep in the back of your mind that you should be looking for
    // better data structures here.
    /// Get the first moved child, if there is one.
    fn moved_child(&self) -> Option<&Move> {
        self.fields
            .iter()
            .map(|f| f.mov.as_ref().or_else(|| f.moved_child()))
            .find(|e| e.is_some())
            .flatten()
    }

    /// Make sure that there are at least `n` fields
    fn ensure_fields(&mut self, n: usize) {
        let len = self.fields.len();
        let extra = n.saturating_sub(len);
        self.fields
            .extend(std::iter::repeat(MoveTree::default()).take(extra));
    }

    /// Do a mutating tree merge between this and another `MoveTree`, with
    /// left-precedence. This is called `extend` to match the api of
    /// `std::collections::HashMap`.
    ///
    /// Invariant: `self` and `other` refer to the same path
    fn extend(&mut self, other: MoveTree) {
        if let (None, m @ Some(_)) = (&mut self.mov, other.mov) {
            self.mov = m
        };
        // Before we finish the merge, there must be at least as many fields in
        // `self` as in `other`.
        self.ensure_fields(other.fields.len());
        // Finally, recurse on the subtrees
        for (fl, fr) in self.fields.iter_mut().zip(other.fields.into_iter()) {
            fl.extend(fr);
        }
    }

    /// Add a move at this point, and return a pair of moves if this is a new
    /// double-move.
    fn update(&mut self, mov: Move) -> Option<(Move, Move)> {
        use MoveKind::*;
        match (&self.mov, &mov.kind) {
            (None, Full) => {
                if let Some(m) = self.moved_child() {
                    return Some((m.clone(), mov));
                }
                self.mov = Some(mov);
            }
            (Some(m), _) => return Some((m.clone(), mov)),
            _ => {}
        }
        None
    }
}

struct DoubleMove {
    fst: Span,
    snd: Span,
}

/// Counts how many times a local has been moved.
#[derive(Default, PartialEq, Eq, Clone, Debug)]
pub struct MoveState {
    /// This map points to the location of the first move of each local that is
    /// not currently live.
    pub moves: HashMap<LocalId, MoveTree>,
    pub double_moves: HashMap<Place, (Move, Move)>,
}

impl MoveState {
    fn get_mut(&mut self, place: &Place) -> Option<&mut MoveTree> {
        self.moves.get_mut(&place.root).map(|mut node| {
            // Because only `Field` elements of a `Place` denote actual memory
            // offsets, we can just walk over those.
            for field in place.iter_fields().copied() {
                node = &mut node.fields[field];
            }
            node
        })
    }

    /// Insert a move at the *end* of a path
    fn insert_move(&mut self, place: &Place, site: Span) {
        let MoveState {
            ref mut moves,
            ref mut double_moves,
        } = self;

        let mut node = moves.entry(place.root).or_insert(MoveTree::default());

        for field in place.iter_fields() {
            // Then this with an intermediate ('partial move')
            if let Some(moves) = node.update(Move::partial(site)) {
                double_moves.insert(place.clone(), moves);
            }
            // Make sure there are enough fields in the tree to take the next step
            node.ensure_fields(*field + 1);
            node = &mut node.fields[*field];
        }
        // Update the final path element ('full move')
        if let Some(moves) = node.update(Move::full(site)) {
            double_moves.insert(place.clone(), moves);
        }
    }

    /// Update the move state with a new operand use, adding anything linear to
    /// the moved list.
    fn move_from(&mut self, arg: &Operand, span: Span) {
        if let Operand::Move(place) = arg {
            self.insert_move(place, span);
        }
    }

    /// Update a variable into which a value has been moved by taking it off the
    /// moved list.
    fn move_into(&mut self, place: &Place) {
        self.get_mut(place).map(|node| node.mov = None);
    }
}

impl Lattice for MoveState {
    fn join(mut self, other: Self) -> Self {
        // We choose to extend a copy of the hashmap, overwriting `Span`s that
        // might be in there. That's ok: if we're merging from two paths, we
        // only care if at least one of them has moved something.
        //
        // Note as above, all the clones might be expensive.
        for (local, other) in other.moves {
            match self.moves.entry(local) {
                Entry::Occupied(mut e) => e.get_mut().extend(other),
                Entry::Vacant(e) => {
                    e.insert(other.clone());
                }
            }
        }
        // TODO it's an important condition to check that the `double_moves`
        // join operation is consistent with the `moves` join operation. They
        // might not be!

        // We can't just use the `extend` API because `Place` is not `Copy`. We
        // could of course derive it, but I want to be careful about not copying
        // too many of them.
        for (place, moves) in &other.double_moves {
            // FIXME Ach, two lookups. This can be done with `raw_entry_mut`,
            // which is an unstable library feature.
            if self.double_moves.get(place).is_none() {
                println!("double move");
                self.double_moves.insert(place.clone(), moves.clone());
            }
        }
        self
    }
}

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure.
pub struct LinearityAnalysis {}

impl DataflowAnalysis<Forward, Blockwise> for LinearityAnalysis {
    type Domain = MoveState;

    fn bottom(&self) -> Self::Domain {
        Self::Domain {
            moves: HashMap::new(),
            double_moves: HashMap::new(),
        }
    }

    fn transfer_stmt_post(&self, state: &mut Self::Domain, stmt: &Stmt, _pt: GraphPt) {
        // NOTE this pattern is repeated in a lot of these analyses. Consider an
        // abstraction.
        let (place, rhs) = match &stmt.kind {
            StmtKind::Assn(place, rhs) => (place.clone(), rhs),
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
            RvalueKind::Ref(_, _) => {
                // TODO Well, this really is what it's all about, isn't it? For
                // now, I suppose, we'll not do anything here at all, and let
                // references move around freely.
            }
        }
        state.move_into(&place);
    }

    fn transfer_block_post(&self, _state: &mut Self::Domain, _block: &BlockKind, _pt: GraphPt) {
        // TODO
    }

    fn initial_state(&self, _blk: BlockId) -> Self::Domain {
        Self::Domain::default()
    }
}
