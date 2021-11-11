//! Assign a fresh lifetime to every `Ref` type.
//!
//! It seems preferable to number lifetimes in the *first* place here, rather
//! than to store them in the types themselves, then hassle with renumbering as
//! rustc does. It's possible that I'll run into more of a mess later on because
//! of this, but it seems sensible to do the simplest thing first. Here are some
//! of the difficulties of the rustc approach:
//!
//! * You need to renumber _something_, _somewhere_, at least to resolve
//!   a function signature to "monotypes."
//! * You lose the ability to check type equality by comparing ids, and have to
//!   instead write a recursive comparinson function matching on both types.
//!
//! Difficulties with this approach:
//!
//! * It's a bit heavy-handed. Potentially slow? Maybe there are more lifetimes
//!   than there need to be? If I write `let y = &x; let z = x;`, should `z` and
//!   `x` have equal lifetimes, or should they have *the same* lifetimes? Or are
//!   they not even equal?
//!
//! * It's a bit "hacky"/unprincipled? the lifetimes really *are* conceptually
//!   part of the types.
//!
//! NOTE: this does not yet handle function arguments!
//!
//! TODO: use the generic `PlaceTree` type instead of the ad hoc one here.

use std::{
    collections::{BTreeMap, HashMap},
    marker::PhantomData,
};

use crate::{
    analysis::dataflow::{DataflowCtx, Forward, OrderProvider},
    mir::*,
    source::Span,
    store::Store,
    store_type,
    types::{RefKind, TyId, Type, TypeInterner},
    util::FmtWith,
};

use super::{
    regions::{LifetimeStore, LtId},
    util::enumerate_stmts,
};

store_type! { LoanStore: LoanId -> Loan }

pub fn ascribe<'l, 'a>(
    lifetimes: &'l mut LifetimeStore,
    context: &'a DataflowCtx,
) -> AscriptionStore<'a> {
    let mut ascriber = Ascriber::new(lifetimes, context);
    // Variables may have lifetimes, depending on their type
    for local in context.gr.locals.iter() {
        ascriber.ascribe_local(local);
    }
    // Loans also have lifetimes. They may coincide with the lifetime of the
    // borrower, but they don't need to!
    ascriber.ascribe_loans(context.gr);

    ascriber.ascriptions
}

/// all the ascriptions for this graph: we hang lifetimes on the branches of
/// each `Place` tree, and associate one with each reference we take.
///
/// NOTE: we could use better data structures here. For one thing, `Loan`s
/// could(/should?) live in a prefix tree, which could simply be fused with the
/// ascriptions tree, and collected with the `ascribe_loans` method.
///
/// But we're absolutely, unequivocally not going to waste a single hour on
/// making anything clever or correct or even asymptotically optimal.
pub struct AscriptionStore<'g> {
    /// For each local, what lifetimes is it ascribed, and where is it borrowed?
    pub locals: Store<LocalId, Option<AscrNode>>,
    /// Every loan (`Ascr` * `Place`) in the CFG
    pub loans: Store<LoanId, Loan>,
    /// Ascriptions to `Ref` statements at each point: the indirection here
    /// supports later borrowchecker analyses that will need to look up loans by
    /// `LoanId`.
    pub refs: BTreeMap<GraphPt, LoanId>,
    _d: PhantomData<&'g ()>,
}

impl<'g> AscriptionStore<'g> {
    fn new() -> Self {
        Self {
            locals: Store::new(),
            loans: Store::new(),
            refs: BTreeMap::new(),
            _d: PhantomData,
        }
    }

    pub fn get_ref(&self, pt: &GraphPt) -> Option<&Loan> {
        self.refs.get(pt).map(|id| &self.loans[*id])
    }

    /// Get all the livetime ascriptions to the type of `local`.
    pub fn local_ascriptions(&self, local: LocalId) -> impl Iterator<Item = Ascr> + '_ {
        self.place_ascriptions(&<Place>::from(local))
    }

    pub fn place_node(&self, place: &Place) -> Option<&AscrNode> {
        let mut node = self.locals[place.root].as_ref();
        let mut projections = place.path.iter();
        while let Some(ascrs) = node {
            node = match projections.next() {
                Some(Proj::Field(n)) => ascrs.slots[*n].as_ref(),
                Some(Proj::Deref) => ascrs.slots[0].as_ref(),
                None => break,
            };
        }
        node
    }

    /// Get all the lifetime ascriptions to the type of `place`.
    pub fn place_ascriptions<'a>(&'a self, place: &Place) -> impl Iterator<Item = Ascr> + 'a {
        self.place_node(place)
            .map(|node| node.iter())
            .into_iter()
            .flatten()
    }
}

/// This bit of machinery builds the ascriptions tree, temporarily holding on to
/// the inherited global state
struct Ascriber<'l, 'a> {
    ascriptions: AscriptionStore<'a>,
    lifetimes: &'l mut LifetimeStore,
    /// The lifetime of references that extend into the caller. There should be
    /// possibly many of these for parameters with different lifetimes, but we
    /// will temporarily simplify the problem by using only (at most) one.
    end: Option<LtId>,
    types: &'a TypeInterner,
    /// The length of each block in the CFG, includin its tail
    block_sizes: &'a [usize],
}

impl<'l, 'a> Ascriber<'l, 'a> {
    fn new(lifetimes: &'l mut LifetimeStore, context: &'a DataflowCtx<'a>) -> Self {
        Self {
            ascriptions: AscriptionStore::new(),
            lifetimes,
            end: None,
            types: &context.ctx.types,
            block_sizes: &context.block_sizes,
        }
    }

    fn new_lifetime(&mut self, is_end: bool) -> LtId {
        let block_sizes = &self.block_sizes;
        if is_end {
            let lifetimes = &mut self.lifetimes;
            *self
                .end
                .get_or_insert_with(|| lifetimes.end_region(block_sizes))
        } else {
            self.lifetimes.new_region(block_sizes)
        }
    }

    fn ascribe_loans(&mut self, gr: &Graph) {
        // Doesn't matter what order we traverse the graph in; this is just a summary pass
        for (loc, stmt) in enumerate_stmts(gr) {
            if let StmtKind::Assn(
                _,
                Rvalue {
                    data: RvalueKind::Ref(kind, rhs),
                    span,
                },
            ) = &stmt.kind
            {
                let lt = self.new_lifetime(false);

                let ascr = Ascr { kind: *kind, lt };
                let loan = Loan {
                    ascr,
                    span: *span,
                    place: rhs.clone(),
                    pt: loc,
                };
                let id = self.ascriptions.loans.insert(loan);
                let key = self.ascriptions.refs.insert(loc, id);
                // We better visit each line only once!
                debug_assert_eq!(key, None);
            };
        }
    }

    /// Assumption: locals arrive in the same order the `Graph` keeps them in.
    fn ascribe_local(&mut self, local: &Local) {
        let is_end = local.kind == LocalKind::Param;
        let node = self.node_from_ty(local.ty, is_end);
        self.ascriptions.locals.insert(node);
    }

    fn node_from_ty(&mut self, ty: TyId, is_end: bool) -> Option<AscrNode> {
        if ty.is_owned(self.types) {
            return None;
        }

        match &self.types[ty] {
            Type::Tuple(tys) => self.node_from_inners(None, tys, is_end),
            Type::Array(ty, _) => self.node_from_inners(None, &[*ty], is_end),
            // FIXME
            Type::Func(_, _) => todo!(),
            // FIXME
            Type::UserType(_) => None,
            Type::Ref(kind, _, ty) => {
                let lt = self.new_lifetime(is_end);
                let ascr = Ascr { kind: *kind, lt };
                self.node_from_inners(Some(ascr), &[*ty], is_end)
            }
            _ => None,
        }
    }

    fn node_from_inners(
        &mut self,
        lt: Option<Ascr>,
        inners: &[TyId],
        is_end: bool,
    ) -> Option<AscrNode> {
        let inners = inners
            .iter()
            .map(|ty| self.node_from_ty(*ty, is_end))
            .collect();
        let node = AscrNode {
            this: lt,
            slots: inners,
        };
        Some(node)
    }
}

/// The actual ascription data
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ascr {
    pub kind: RefKind,
    pub lt: LtId,
}

impl Ascr {
    pub fn is_uniq(&self) -> bool {
        self.kind == RefKind::Uniq
    }

    pub fn is_shrd(&self) -> bool {
        self.kind == RefKind::Shrd
    }
}

/// The ascription data of a reference, together with the `Place` it references.
/// See [computing loans in
/// scope](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#borrow-checker-phase-1-computing-loans-in-scope)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loan {
    pub ascr: Ascr,
    pub place: Place,
    pub span: Span,
    pub pt: GraphPt,
}

impl Loan {
    pub fn is_uniq(&self) -> bool {
        self.ascr.is_uniq()
    }

    pub fn is_shrd(&self) -> bool {
        self.ascr.is_shrd()
    }
}

#[derive(Debug)]
pub struct AscrNode {
    /// Ascription at this `Place`
    pub this: Option<Ascr>,
    /// Ascriptions at deeper paths
    pub slots: Vec<Option<AscrNode>>,
}

impl AscrNode {
    // NOTE: can't use an opaque type (`impl Iterator<..>`) because of recursion
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Ascr> + 'a> {
        let children = self
            .slots
            .iter()
            .map(|slot| slot.iter().map(|asc| asc.iter()).flatten())
            .flatten();
        Box::new(self.this.iter().cloned().chain(children))
    }
}

// == boilerplate impls ==

impl std::fmt::Display for Ascr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.kind, self.lt)
    }
}

impl std::fmt::Display for LoanId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "l{}", self.0)
    }
}
