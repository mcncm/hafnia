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
    types::{CachedTypeInterner, TyId, Type},
};

use super::{util::enumerate_stmts, LifetimeStore, LtId};

pub fn ascribe<'l, 'a>(
    lifetimes: &'l mut LifetimeStore,
    context: &'a DataflowCtx,
) -> Ascriptions<'a> {
    let mut ascriber = Ascriber::new(lifetimes, context);
    for local in context.gr.locals.iter() {
        ascriber.ascribe_local(local);
    }

    ascriber.ascribe_refs(&context.gr);

    ascriber.ascriptions
}

/// all the ascriptions for this graph: we hang lifetimes on the branches of
/// each `Place` tree, and associate one with each reference we take.
pub struct Ascriptions<'g> {
    /// Lifetime ascriptions of locals types
    pub locals: Store<LocalId, Option<AscriptionNode>>,
    /// Ascriptions to `Ref` statements
    pub refs: BTreeMap<GraphPt, LtId>,
    _d: PhantomData<&'g ()>,
}

impl LifetimeStore {
    fn new_region(&mut self) -> LtId {
        let lifetime = super::Lifetime {
            pts: std::collections::BTreeSet::new(),
        };
        self.insert(lifetime)
    }
}

/// This bit of machinery builds the ascriptions tree, temporarily holding on to
/// the inherited global state
struct Ascriber<'l, 'a> {
    ascriptions: Ascriptions<'a>,
    lifetimes: &'l mut LifetimeStore,
    types: &'a CachedTypeInterner,
}

impl<'l, 'a> Ascriber<'l, 'a> {
    fn new(lifetimes: &'l mut LifetimeStore, context: &DataflowCtx<'a>) -> Self {
        Self {
            ascriptions: Ascriptions::new(),
            lifetimes,
            types: &context.ctx.types,
        }
    }

    fn ascribe_refs(&mut self, gr: &Graph) {
        // Doesn't matter what order we traverse the graph in; this is just a summary pass
        for (loc, stmt) in enumerate_stmts(gr) {
            match &stmt.kind {
                StmtKind::Assn(
                    _,
                    Rvalue {
                        data: RvalueKind::Ref(_kind, _rhs),
                        span: _,
                    },
                ) => {
                    let lt = self.lifetimes.new_region();
                    let key = self.ascriptions.refs.insert(loc, lt);
                    // We better visit each line only once!
                    debug_assert_eq!(key, None);
                }
                _ => {}
            };
        }
    }

    /// Assumption: locals arrive in the same order the `Graph` keeps them in.
    fn ascribe_local(&mut self, local: &Local) {
        let node = self.node_from_ty(local.ty);
        self.ascriptions.locals.insert(node);
    }

    fn node_from_ty(&mut self, ty: TyId) -> Option<AscriptionNode> {
        let ty = &self.types[ty];
        if ty.is_owned(self.types) {
            return None;
        }

        match ty {
            Type::Tuple(tys) => self.node_from_inners(None, tys),
            Type::Array(ty) => self.node_from_inners(None, &[*ty]),
            // FIXME
            Type::Func(_, _) => todo!(),
            // FIXME
            Type::UserType(_) => None,
            Type::Ref(_ref, ty) => {
                let lt = self.lifetimes.new_region();
                self.node_from_inners(Some(lt), &[*ty])
            }
            _ => None,
        }
    }

    fn node_from_inners(&mut self, lt: Option<LtId>, inners: &[TyId]) -> Option<AscriptionNode> {
        let inners = inners.iter().map(|ty| self.node_from_ty(*ty)).collect();
        let node = AscriptionNode {
            this: lt,
            slots: inners,
        };
        Some(node)
    }
}

impl<'g> Ascriptions<'g> {
    fn new() -> Self {
        Self {
            locals: Store::new(),
            refs: BTreeMap::new(),
            _d: PhantomData,
        }
    }
}

/// Ok, this is a bit of an odd tree, but it might actually be the most efficient in
/// practice, noting that few variables will have wide-branching `Place` trees.
pub struct AscriptionNode {
    /// Ascroption at this `Place`
    this: Option<LtId>,
    /// Ascriptions at deeper paths
    slots: Vec<Option<AscriptionNode>>,
}

impl AscriptionNode {
    // NOTE: can't use an opaque type (`impl Iterator<..>`) because of recursion
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = LtId> + 'a> {
        let children = self
            .slots
            .iter()
            .map(|slot| slot.iter().map(|asc| asc.iter()).flatten())
            .flatten();
        Box::new(self.this.iter().cloned().chain(children))
    }
}
