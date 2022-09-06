use std::collections::{hash_map::Entry, HashMap, HashSet};

use super::dataflow::{Blockwise, DataflowAnalysis, DataflowCtx, DataflowRunner, Forward, Lattice};
use crate::{hafnia_errors::ErrorBuf, mir::*, place_tree, source::Span, types::RefKind};

pub fn check_linearity(context: &DataflowCtx, errs: &mut ErrorBuf) {
    let linearity_ana = LinearityAnalysis {
        locals: context.gr.locals.len(),
    };
    let moves = &DataflowRunner::new(linearity_ana, &context)
        .run()
        // This is sort of, but not *quite* correct. I can't fix it right
        // now, but it is a little troubling.
        .block_states[context.gr.exit_block];
    for (_local, (fst, snd)) in moves.double_moves.iter() {
        // TODO different messages for partial moves
        match snd {
            SecondUse::Move(mov) => {
                errs.push(errors::DoubleMove {
                    fst: fst.site,
                    snd: mov.site,
                });
            }
            SecondUse::Borrow(bor) => {
                errs.push(errors::BorrowAfterMove {
                    fst: fst.site,
                    snd: bor.site,
                });
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MoveKind {
    /// A field of this data was moved
    Partial,
    /// This whole object was moved
    Full,
}

/// An illegal second use of an already-moved `Place`
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SecondUse {
    Move(Move),
    Borrow(Borrow),
}

impl From<Move> for SecondUse {
    fn from(mov: Move) -> Self {
        Self::Move(mov)
    }
}

impl From<Borrow> for SecondUse {
    fn from(borrow: Borrow) -> Self {
        Self::Borrow(borrow)
    }
}

/// A case of a `Place` being moved
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Move {
    pub kind: MoveKind,
    pub site: Span,
}

/// A case of a `Place` being borrowed
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Borrow {
    pub kind: RefKind,
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

type MoveTree = place_tree::PlaceNode<Move>;

/// Counts how many times a local has been moved.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct MoveState {
    /// This map points to the location of the first move of each local that is
    /// not currently live.
    pub moves: place_tree::PlaceStore<Move>,
    pub double_moves: HashMap<Place, (Move, SecondUse)>,
}

impl MoveState {
    fn get_node_mut(&mut self, place: &Place) -> Option<&mut MoveTree> {
        self.moves.get_node_mut(place)
    }

    fn get_move(&self, place: &Place) -> Option<&Move> {
        self.moves.get(place)
    }

    /// Insert a move at the *end* of a path, optionally returning a conflicting
    /// move, and possibly providing a new node at the specified place.
    fn traverse_move_path(&mut self, place: &Place, new: Option<Move>) -> Option<Move> {
        let mut ancestor = None;
        let node = self.moves.create_node_with(place, |anc| {
            if ancestor.is_none() && anc.is_some() {
                ancestor = anc.clone();
            }
        });
        //Is there any "get_or_insert" with an optional insert?
        let prev = node.this.clone().or(ancestor.or_else(|| {
            // A bit of an odd choice of iterator, but it works
            let mut children = node
                .slots
                .iter()
                .filter_map(|node| node.as_ref().map(|node| node.iter_post()))
                .flatten();
            children.next().cloned()
        }));
        if new.is_some() {
            node.this = new;
        }
        prev
    }

    /// Update the move state with a new operand use, adding anything linear to
    /// the moved list.
    fn move_from(&mut self, arg: &Operand, span: Span) {
        if let Operand::Move(place) = arg {
            let mov = Move {
                kind: if place.path.is_empty() {
                    MoveKind::Full
                } else {
                    MoveKind::Partial
                },
                site: span,
            };
            if let Some(prev) = self.traverse_move_path(place, Some(mov.clone())) {
                self.double_moves.insert(place.clone(), (prev, mov.into()));
            }
        }
    }

    /// Update a variable into which a value has been moved by taking it off the
    /// moved list.
    fn move_into(&mut self, place: &Place) {
        let node = self.moves.create_node(place);
        node.this = None;
    }

    fn borrow_from(&mut self, kind: RefKind, place: &Place, span: Span) {
        let snd = Borrow { kind, site: span }.into();
        if let Some(prev) = self.traverse_move_path(place, None) {
            self.double_moves.insert(place.clone(), (prev, snd));
        }
    }
}

impl Lattice for MoveState {
    fn join(mut self, other: Self) -> Self {
        self.moves.extend(other.moves);
        self.double_moves.extend(other.double_moves);
        self
    }
}

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure.
pub struct LinearityAnalysis {
    // Number of locals
    locals: usize,
}

impl DataflowAnalysis<Forward, Blockwise> for LinearityAnalysis {
    type Domain = MoveState;

    fn bottom(&self) -> Self::Domain {
        Self::Domain {
            moves: place_tree::PlaceStore::new(self.locals),
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
            RvalueKind::Ref(kind, place) => {
                // TODO Well, this really is what it's all about, isn't it? For
                // now, I suppose, we'll not do anything here at all, and let
                // references move around freely.
                state.borrow_from(*kind, place, rhs.span);
            }
            RvalueKind::Array(items) => {
                // FIXME this span is non-ideal
                items
                    .iter()
                    .for_each(|item| state.move_from(item, rhs.span));
            }
        }
        state.move_into(&place);
    }

    fn transfer_block_post(&self, state: &mut Self::Domain, block: &BlockKind, _pt: GraphPt) {
        match block {
            BlockKind::Goto(_) => {}
            // Right now we only switch on copyable data, anyway.
            BlockKind::Switch(_) => {}
            BlockKind::Call(call) => {
                state.move_into(&call.ret);
            }
            BlockKind::Ret => {}
        }
    }

    fn initial_state(&self, _blk: BlockId) -> Self::Domain {
        self.bottom()
    }
}

mod errors {
    use crate::source::Span;
    use hafnia_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[msg = "moved affine data twice"]
    pub struct DoubleMove {
        #[span(msg = "this data was first moved here...")]
        /// The first use site
        pub fst: Span,
        #[span(msg = "...and then moved again here")]
        /// The second use site
        pub snd: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "borrowed previously-moved data"]
    pub struct BorrowAfterMove {
        #[span(msg = "the data was first moved here...")]
        /// The first use site
        pub fst: Span,
        #[span(msg = "...and then borrowed here")]
        /// The second use site
        pub snd: Span,
    }
}
