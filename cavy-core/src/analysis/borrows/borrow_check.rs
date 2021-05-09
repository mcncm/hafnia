//! The second borrow-checking phase, per [Borrow checker phase
//! 2](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#borrow-checker-phase-2-reporting-errors)
use super::{
    ascription::Loan,
    loan_scope::{LoanId, LocalLoans},
    regions::RegionInf,
    util,
};
use crate::{
    analysis::{dataflow::StmtStates, DataflowCtx},
    cavy_errors::ErrorBuf,
    context::Context,
    mir::*,
    source::Span,
    types::{CachedTypeInterner, RefKind},
};

pub fn borrow_check(
    regions: &RegionInf,
    scopes: &StmtStates<LocalLoans>,
    context: &DataflowCtx,
    errs: &mut ErrorBuf,
) {
    let bc = BorrowChecker {
        regions,
        scopes,
        context,
        errs,
    };
    bc.run();
}

struct BorrowChecker<'a> {
    regions: &'a RegionInf<'a>,
    scopes: &'a StmtStates<LocalLoans>,
    context: &'a DataflowCtx<'a>,
    errs: &'a mut ErrorBuf,
}

impl<'a> BorrowChecker<'a> {
    fn run(mut self) {
        let actions = ActionStream::new(&self.context);
        for action in actions {
            self.check(action);
        }
    }

    /// Virtually identical to the pseudocode function `access_legal` in the RFC
    fn check(&mut self, action: Action<'a>) {
        // NOTE: why are they called 'borrows' here in the RFC, rather than
        // 'loans'? Aren't they talking about loans?
        for ln in self.scopes[action.pt].iter() {
            let loan = &self.regions.ascriptions.loans[ln];
            if action.is_relevant(loan, self.context) {
                self.validate(&action, loan)
            }
        }
    }

    /// Check and report errors
    fn validate<'b>(&mut self, action: &'b Action<'a>, loan: &'b Loan) {
        if !(action.is_read() && loan.is_shrd()) {
            self.errs.push(errors::BorrowCheckError {
                verb: action.kind.verb(),
                verb_participle: action.kind.verb_participle(),
                borrow_participle: borrow_participle(loan),
                loan: loan.span,
                action: action.span,
            });
        }
    }
}

/// The image of the 'action' abstraction function described in the RFC.
#[derive(Debug)]
struct Action<'p> {
    kind: ActionKind,
    place: &'p Place,
    pt: GraphPt,
    span: Span,
}

impl<'p> Action<'p> {
    fn depth(&self) -> ActionDepth {
        self.kind.attributes().0
    }

    fn direction(&self) -> ActionDirection {
        self.kind.attributes().1
    }

    fn is_read(&self) -> bool {
        matches!(self.direction(), ActionDirection::Read)
    }

    fn is_shallow(&self) -> bool {
        matches!(&self.depth(), ActionDepth::Shallow)
    }

    /// Check if a loan is "relevant" to this action
    fn is_relevant(&self, loan: &Loan, context: &DataflowCtx) -> bool {
        // it's a loan against the lvalue or a (strict) prefix of it
        loan.place.is_prefix(self.place)
            || if self.is_shallow() {
                // the lvalue is a so-called "shallow prefix" of the loan place
                self.place.is_shallow_prefix(&loan.place)
            } else {
                self.place
                    .is_supporting_prefix(&loan.place, context.gr, context.ctx)
            }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ActionDepth {
    Shallow,
    Deep,
}

// A funny name for this enum, but it's what I've got for the moment.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ActionDirection {
    Read,
    Write,
}

/// Rather than an enum `DeepWrite | DeepRead | ShallowWrite`, as suggested in
/// the RFC, we'll use an abstraction function with a whole host of
/// `ActionKind`s, each of which has a depth (`Shallow`, `Deep`) and a direction
/// (`Read`, `Write`) as an attribute.
#[derive(Debug)]
enum ActionKind {
    /// Move from
    Move,
    /// Copy from
    Copy,
    /// Assign to
    Assn,
    /// Condition on, immutably: this is a guard that should satisfy the
    /// "observational immutability criterion".
    GuardImmut,
    /// condition on, mutably: this is a guard that could change after exiting
    /// the guarded block(s).
    GuardMut,
    /// Take a referenceto
    Borrow(RefKind),
    /// Drop the `Place` (combining what rustc calls dropping and
    /// `StorageDead`).
    Drop,
}

impl ActionKind {
    fn attributes(&self) -> (ActionDepth, ActionDirection) {
        use ActionDepth::*;
        use ActionDirection::*;
        use ActionKind::*;
        match self {
            Move => (Deep, Write),
            Copy => (Deep, Read),
            Assn => (Shallow, Write),
            GuardImmut => (Deep, Read),
            GuardMut => (Deep, Write),
            Borrow(kind) => {
                let direction = match kind {
                    RefKind::Shrd => Read,
                    RefKind::Uniq => Write,
                };
                (Deep, direction)
            }
            Drop => (Deep, Write),
        }
    }
}

// NOTE: this is really just a lazy version of the `Summaryrunner`. I should
// really just use that/unify the data structures. But, today, resist the siren
// song of abstraction.
struct ActionStream<'a> {
    ctx: &'a Context<'a>,
    locals: &'a LocalStore,
    // Note: we *could* make `Graph::iter` return an `std::iter::Slice` instead
    // of an opaque type, and not need the indirection. But it seems safer and
    // wiser to use the most general type where possible.
    blockstream: Box<dyn Iterator<Item = (BlockId, &'a BasicBlock)> + 'a>,
    pt: GraphPt,
    // The statements of the current block
    stmts: std::slice::Iter<'a, Stmt>,
    // The tail of the current block; `None` if it has been consumed
    tail: Option<&'a BlockKind>,
    actionbuf: Vec<Action<'a>>,
}

impl<'a> ActionStream<'a> {
    fn new(context: &'a DataflowCtx) -> Self {
        let mut blocks = context.gr.idx_enumerate();
        let (blk, block) = blocks.next().expect("CFG without any blocks");
        Self {
            ctx: &context.ctx,
            locals: &context.gr.locals,
            blockstream: Box::new(blocks),
            pt: GraphPt::first(blk),
            stmts: block.stmts.iter(),
            tail: Some(&block.kind),
            actionbuf: Vec::new(),
        }
    }

    fn consume_block(&mut self, blk: BlockId, block: &'a BasicBlock) {
        self.stmts = block.stmts.iter();
        self.pt = GraphPt::first(blk);
        self.tail = Some(&block.kind);
    }

    fn consume_stmt(&mut self, stmt: &'a Stmt) {
        match &stmt.kind {
            StmtKind::Assn(lhs, rhs) => {
                self.action(lhs, ActionKind::Assn, stmt.span);
                self.consume_rvalue(&rhs.data, rhs.span);
            }
            StmtKind::Assert(_) => {}
            StmtKind::Drop(place) => {
                // NOTE: as per RFC comment, this might be more conservative
                // than necessary.
                self.action(place, ActionKind::Drop, stmt.span);
            }
            StmtKind::Io(_) => {}
            StmtKind::Nop => {}
        }
    }

    fn consume_rvalue(&mut self, rvalue: &'a RvalueKind, span: Span) {
        // Some of these spans are... not good.
        match rvalue {
            RvalueKind::BinOp(_, lop, rop) => {
                self.consume_operand(lop, span);
                self.consume_operand(rop, span);
            }
            RvalueKind::UnOp(_, op) => {
                self.consume_operand(op, span);
            }
            RvalueKind::Ref(kind, place) => {
                self.action(place, ActionKind::Borrow(*kind), span);
            }
            RvalueKind::Use(op) => {
                self.consume_operand(op, span);
            }
        }
    }

    fn consume_operand(&mut self, op: &'a Operand, span: Span) {
        let place = match op.place() {
            Some(place) => place,
            None => return,
        };

        let ty = self.locals.type_of(place, &self.ctx);
        let kind = if ty.is_affine(&self.ctx) {
            ActionKind::Move
        } else {
            ActionKind::Copy
        };
        self.action(place, kind, span);
    }

    fn consume_tail(&mut self, tail: &'a BlockKind) {
        // These spans are *really* not very precise.
        match tail {
            BlockKind::Goto(_) => {}
            BlockKind::Switch(switch) => {
                // Nothing in a condition must be linear, so we can use
                // `DeepRead` unconditionally.
                //
                // No, that's not true; it could be classical, and we could
                // overwrite it.
                let ty = self.locals.type_of(&switch.cond, &self.ctx);
                let kind = if ty.is_coherent(&self.ctx) {
                    ActionKind::GuardImmut
                } else {
                    ActionKind::GuardMut
                };
                self.action(&switch.cond, kind, switch.span);
            }
            BlockKind::Call(call) => {
                // The lhs of a call should be treated just like the lhs of an
                // `Assn`.
                self.action(&call.ret, ActionKind::Assn, call.span);
                for arg in &call.args {
                    self.consume_operand(arg, call.span);
                }
            }
            BlockKind::Ret => {}
        }
    }

    fn action(&mut self, place: &'a Place, kind: ActionKind, span: Span) {
        self.actionbuf.push(Action {
            kind,
            place,
            pt: self.pt,
            span,
        })
    }
}

impl<'a> Iterator for ActionStream<'a> {
    type Item = Action<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.actionbuf.is_empty() {
            // Puzzle: can you simplify this with an iterator adapter chain?
            match self.stmts.next() {
                Some(stmt) => {
                    self.consume_stmt(stmt);
                    self.pt.stmt += 1;
                }
                None => match self.tail.take() {
                    Some(tail) => self.consume_tail(tail),
                    None => match self.blockstream.next() {
                        Some((blk, block)) => {
                            self.pt = GraphPt::first(blk);
                            self.consume_block(blk, block);
                        }
                        None => break,
                    },
                },
            }
        }

        self.actionbuf.pop()
    }
}

mod errors {
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[msg = "tried to {verb} borrowed data"]
    pub struct BorrowCheckError {
        pub verb: &'static str,
        pub verb_participle: &'static str,
        pub borrow_participle: &'static str,
        #[span(msg = "the data was {borrow_participle} here...")]
        pub loan: Span,
        #[span(msg = "...and later {verb_participle} here.")]
        pub action: Span,
    }
}

/*
Some text representations of the actions
*/

impl ActionKind {
    /// A helpful string to use in the error message
    fn verb(&self) -> &'static str {
        use ActionKind::*;
        use RefKind::*;
        match self {
            Move => "move",
            Copy => "copy",
            Assn => "assign to",
            GuardImmut => "control on",
            GuardMut => "control on",
            Borrow(Uniq) => "uniquely borrow",
            Borrow(Shrd) => "borrow",
            Drop => "drop",
        }
    }

    /// Another helpful string to use in the error message
    fn verb_participle(&self) -> &'static str {
        use ActionKind::*;
        use RefKind::*;
        match self {
            Move => "moved",
            Copy => "copied",
            Assn => "assigned to",
            GuardImmut => "controlled on",
            GuardMut => "controlled on",
            Borrow(Uniq) => "uniquely borrowed",
            Borrow(Shrd) => "borrowed",
            Drop => "dropped",
        }
    }
}

fn borrow_participle(loan: &Loan) -> &'static str {
    match &loan.ascr.kind {
        RefKind::Shrd => "borrowed",
        RefKind::Uniq => "uniquely borrowed",
    }
}
