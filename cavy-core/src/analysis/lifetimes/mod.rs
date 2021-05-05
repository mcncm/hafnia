//! This module contains the region analysis components implementing the `cavyc`
//! borrow checker. It is based directly on the outline in the [non-lexical
//! lifetimes
//! RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md) by
//! Matsakis et al.

// TODO
// + Collect liveness constraints

use core::fmt;
use std::collections::BTreeSet;

use crate::{context::Context, mir::*};
use crate::{store_type, util::FmtWith};

use super::dataflow::{DataflowCtx, DataflowRunner};

mod ascription;
mod liveness;
mod regions;
mod util;

/// Main entry point for region inference and borrow checking
pub fn borrow_check(context: DataflowCtx) {
    let _lifetimes = regions::infer_regions(&context);
}

// A map from lightweight "lifetime" variables to the regions they represent
store_type! { LifetimeStore : LtId -> Lifetime }

pub struct Lifetime {
    pts: BTreeSet<GraphPt>,
}

impl Lifetime {
    /// Add a single point to the lifetime
    pub fn insert(&mut self, pt: GraphPt) -> bool {
        self.pts.insert(pt)
    }

    pub fn iter(&self) -> impl Iterator<Item = GraphPt> + '_ {
        self.pts.iter().cloned()
    }
}

impl LifetimeStore {
    fn new_region(&mut self) -> LtId {
        let lifetime = Lifetime {
            pts: BTreeSet::new(),
        };
        self.insert(lifetime)
    }
}

impl Place {
    /// The minimum path length for a subpath `Place` to be a supporting prefix
    fn supporting_prefix_len(&self, _ctx: &Context) -> usize {
        let _len = self.path.len();
        for elem in self.path.iter().rev() {
            match elem {
                Proj::Field(_) => {}
                Proj::Deref => {}
            }
        }
        todo!()
    }
}

// === fmt impls ===

impl fmt::Display for LtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", self.0)
    }
}
