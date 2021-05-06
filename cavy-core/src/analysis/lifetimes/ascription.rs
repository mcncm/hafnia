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
//! NOTE this does not yet handle function arguments!

use std::{
    collections::{BTreeMap, HashMap},
    marker::PhantomData,
};

use crate::{
    analysis::dataflow::{DataflowCtx, Forward, OrderProvider},
    mir::*,
    store::Store,
    types::{CachedTypeInterner, RefKind, TyId, Type},
};

use super::{util::enumerate_stmts, LifetimeStore, LtId};

pub fn ascribe<'l, 'a>(
    lifetimes: &'l mut LifetimeStore,
    context: &'a DataflowCtx,
) -> AscriptionStore<'a> {
    let mut ascriber = Ascriber::new(lifetimes, context);
    for local in context.gr.locals.iter() {
        ascriber.ascribe_local(local);
    }

    ascriber.ascribe_refs(&context.gr);

    ascriber.ascriptions
}

/// all the ascriptions for this graph: we hang lifetimes on the branches of
/// each `Place` tree, and associate one with each reference we take.
pub struct AscriptionStore<'g> {
    /// Lifetime ascriptions of locals types
    pub locals: Store<LocalId, Option<AscrNode>>,
    /// Ascriptions to `Ref` statements
    pub refs: BTreeMap<GraphPt, LtAscr>,
    _d: PhantomData<&'g ()>,
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
    types: &'a CachedTypeInterner,
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
            self.end
                .get_or_insert_with(|| lifetimes.end_region(block_sizes))
                .clone()
        } else {
            self.lifetimes.new_region(block_sizes)
        }
    }

    fn ascribe_refs(&mut self, gr: &Graph) {
        // Doesn't matter what order we traverse the graph in; this is just a summary pass
        for (loc, stmt) in enumerate_stmts(gr) {
            match &stmt.kind {
                StmtKind::Assn(
                    _,
                    Rvalue {
                        data: RvalueKind::Ref(kind, _rhs),
                        span: _,
                    },
                ) => {
                    let lt = self.new_lifetime(false);
                    let ascr = LtAscr { kind: *kind, lt };
                    let key = self.ascriptions.refs.insert(loc, ascr);
                    // We better visit each line only once!
                    debug_assert_eq!(key, None);
                }
                _ => {}
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
        let ty = &self.types[ty];
        if ty.is_owned(self.types) {
            return None;
        }

        match ty {
            Type::Tuple(tys) => self.node_from_inners(None, tys, is_end),
            Type::Array(ty) => self.node_from_inners(None, &[*ty], is_end),
            // FIXME
            Type::Func(_, _) => todo!(),
            // FIXME
            Type::UserType(_) => None,
            Type::Ref(kind, ty) => {
                let lt = self.new_lifetime(is_end);
                let ascr = LtAscr { kind: *kind, lt };
                self.node_from_inners(Some(ascr), &[*ty], is_end)
            }
            _ => None,
        }
    }

    fn node_from_inners(
        &mut self,
        lt: Option<LtAscr>,
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

impl<'g> AscriptionStore<'g> {
    fn new() -> Self {
        Self {
            locals: Store::new(),
            refs: BTreeMap::new(),
            _d: PhantomData,
        }
    }

    /// Get all the livetime ascriptions to the type of `local`.
    pub fn local_ascriptions<'a>(&'a self, local: LocalId) -> impl Iterator<Item = LtAscr> + 'a {
        self.place_ascriptions(&<Place>::from(local))
    }

    /// Get all the lifetime ascriptions to the type of `place`.
    pub fn place_ascriptions<'a>(&'a self, place: &Place) -> impl Iterator<Item = LtAscr> + 'a {
        let err = "Attempted to read missing lifetime ascriptions";

        self.locals[place.root]
            .as_ref()
            .and_then(|mut node| {
                for proj in &place.path {
                    node = match proj {
                        Proj::Field(n) => node.slots[*n].as_ref().expect(err),
                        Proj::Deref => node.slots[0].as_ref().expect(err),
                    };
                }
                Some(node.iter())
            })
            .into_iter()
            .flatten()
    }
}

/// The actual ascription data
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LtAscr {
    pub kind: RefKind,
    pub lt: LtId,
}

/// Ok, this is a bit of an odd tree, but it might actually be the most efficient in
/// practice, noting that few variables will have wide-branching `Place` trees.
pub struct AscrNode {
    /// Ascription at this `Place`
    pub this: Option<LtAscr>,
    /// Ascriptions at deeper paths
    pub slots: Vec<Option<AscrNode>>,
}

impl AscrNode {
    // NOTE: can't use an opaque type (`impl Iterator<..>`) because of recursion
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = LtAscr> + 'a> {
        let children = self
            .slots
            .iter()
            .map(|slot| slot.iter().map(|asc| asc.iter()).flatten())
            .flatten();
        Box::new(self.this.iter().cloned().chain(children))
    }
}

// == boilerplate impls ==

impl std::fmt::Display for LtAscr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.kind, self.lt)
    }
}
