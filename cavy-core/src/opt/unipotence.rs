//! This optimization eliminates sequenced operations that compose to the identity.
//! The prototypical example is a pair of consecutive `X`, `Y`, or `Z` gates.
//! This optimization could also be made at the circuit level, but including it
//! here is a good exercise. Note that this is a simple version of this
//! optimization; there's room for it to be made subtantially cleverer!

use std::collections::{hash_map::Entry, HashMap};

use crate::{context::Context, mir::*, source::Span};

pub fn optimize(mir: &mut Mir, _ctx: &Context) {
    for gr in mir.graphs.iter_mut() {
        simpl_graph(gr);
    }
}

fn simpl_graph(gr: &mut Graph) {
    let mut checker = StrandChecker::new();
    for block in gr.iter_mut() {
        let _ = checker.simplify(block);
    }
}

/// a statement location within a basic block
type Loc = usize;

/// Kinds of unipotent operators
#[rustfmt::skip]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum UniKind {
    I, X, Z, H
}

/// An edit takes the form of a pair of statement locations:
///
/// _j = ~ _i;  // fst
/// ...
/// _k = ~ _j;  // snd
///
/// will be rewritten to,
///
/// _k = move _i;
#[derive(Debug)]
struct Edit {
    lhs: Place,
    rhs: Place,
    /// First strand index
    fst: usize,
    /// Second strand index
    snd: usize,
}

#[derive(Debug)]
struct Uni {
    lhs: Place,
    rhs: Place,
    /// Kind of unipotent operation
    kind: UniKind,
    /// Position in the strand
    idx: usize,
}

// NOTE: I think the applicability of this particular optimization will actually
// be somewhat rare. In fact, it might just be special-cased by later ones. But
// these `Strand`s will allocate quite a lot.
#[derive(Debug)]
struct Strand {
    /// Unipotent operators that have been found, but not paired off
    op_stack: Vec<Uni>,
    /// Locations of the strand blocks
    locs: Vec<Loc>,
    /// Edits found so far
    edits: Vec<Edit>,
}

impl Strand {
    fn new() -> Self {
        Self {
            op_stack: vec![],
            locs: vec![],
            edits: vec![],
        }
    }

    fn insert(&mut self, op: UniKind, loc: Loc, places: (Place, Place)) {
        if let UniKind::I = op {
            return;
        }

        let op = Uni {
            kind: op,
            lhs: places.0,
            rhs: places.1,
            idx: self.locs.len(),
        };
        self.locs.push(loc);

        // look at the top of the stack
        match self.op_stack.pop() {
            Some(prev) => {
                // for now, all the ops (except I) are order 2
                if op.kind == prev.kind {
                    self.edits.push(Edit {
                        fst: prev.idx,
                        snd: op.idx,
                        rhs: prev.rhs,
                        lhs: op.lhs,
                    });
                } else {
                    self.op_stack.push(prev);
                    self.op_stack.push(op);
                }
            }
            None => self.op_stack.push(op),
        }
    }

    /// Merge the edit intervals
    fn merge(mut self) -> MergedStrand {
        if self.edits.len() == 0 {
            return MergedStrand(self);
        }

        self.edits.sort_by_key(|edit| edit.fst);
        let mut edits = self.edits.drain(0..);
        let mut stack = Vec::new();
        match edits.next() {
            Some(fst) => stack.push(fst),
            None => unreachable!(),
        };
        for edit in edits {
            let prev = stack.last_mut().unwrap();
            // Edits are mergeable if they are merely adjacent
            if edit.fst > prev.snd + 1 {
                stack.push(edit);
            } else {
                prev.snd = edit.snd;
                prev.lhs = edit.lhs;
            }
        }
        std::mem::swap(&mut self.edits, &mut stack);
        MergedStrand(self)
    }
}

struct MergedStrand(Strand);

impl MergedStrand {
    // Must have merged before applying edits
    fn apply(self, block: &mut BasicBlock) {
        let strand = self.0;
        for edit in strand.edits {
            // The beginning of the edit, which is to be excised.
            for loc in strand.locs[edit.fst..edit.snd].iter() {
                block.stmts[*loc].kind = StmtKind::Nop;
            }
            let end = &mut block.stmts[strand.locs[edit.snd]];
            let rvalue = Rvalue {
                data: RvalueKind::Use(Operand::Move(edit.rhs)),
                span: Span::default(), // technically wrong
            };
            end.kind = StmtKind::Assn(edit.lhs, rvalue);
        }
    }
}

struct StrandChecker {
    /// Strands identified by the lhs they assign to. For example, when
    /// encountering the statement,
    ///
    /// _j = ~ _i;
    ///
    /// we will take the strand out of the slot `_i`, and place it into the slot
    /// `_j`.
    live_strands: HashMap<Place, Strand>,
    /// Strands that have been terminated by encountering a BinOp, reaching the
    /// end of a block, etc.
    dead_strands: Vec<MergedStrand>,
}

impl StrandChecker {
    fn new() -> Self {
        Self {
            live_strands: HashMap::new(),
            dead_strands: Vec::new(),
        }
    }

    // Invariant: after simplifying a block, this data structure is empty.
    fn simplify(&mut self, block: &mut BasicBlock) {
        for (loc, stmt) in block.stmts.iter().enumerate() {
            match &stmt.kind {
                StmtKind::Assn(place, rvalue) => {
                    self.ingest_stmt(loc, place, rvalue);
                }
                // Ignore aserts; they're unsafe, anyway
                StmtKind::Assert(_) => {}
                // Should be able to ignore drops, too
                StmtKind::Drop(_) => {}
                // Ignore IO; doesn't classical things don't matter
                StmtKind::Io(_) => {}
                // Of course, ignore
                StmtKind::Nop => {}
            }
        }

        // Dump the remaining live strands at the end of the block
        self.dead_strands
            .extend(self.live_strands.drain().map(|(_, strand)| strand.merge()));

        // Apply the merged strands
        for strand in self.dead_strands.drain(0..) {
            strand.apply(block);
        }
    }

    fn ingest_stmt(&mut self, loc: Loc, place: &Place, rvalue: &Rvalue) {
        use crate::ast::UnOpKind::*;
        use Operand::*;
        use RvalueKind::*;
        let (op, rhs) = match &rvalue.data {
            UnOp(Not, Copy(p)) | UnOp(Not, Move(p)) => (UniKind::X, p),
            UnOp(Split, Move(p)) => (UniKind::H, p),
            Use(Copy(p)) | Use(Move(p)) => (UniKind::I, p),

            UnOp(_, _) | Use(_) => return,

            // Must end a strand if one of its places appears in a binop or ref.
            BinOp(_, lhs, rhs) => {
                self.kill_at_place(lhs.place());
                self.kill_at_place(rhs.place());
                return;
            }
            Ref(_, rhs) => {
                self.kill_at_place(Some(rhs));
                return;
            }
            // Let's wimp out here
            Array(_items) => return,
        };

        // Take the strand out of its old place
        let mut strand = match self.live_strands.entry(rhs.clone()) {
            Entry::Occupied(e) => e.remove(),
            Entry::Vacant(_) => Strand::new(),
        };

        // Put it in its new place
        strand.insert(op, loc, (place.clone(), rhs.clone()));
        self.live_strands.insert(place.clone(), strand);
    }

    fn kill_at_place(&mut self, place: Option<&Place>) {
        if let Some(place) = place {
            let dead_strands = &mut self.dead_strands;
            self.live_strands
                .remove(place)
                .map(|strand| dead_strands.push(strand.merge()));
        }
    }
}
