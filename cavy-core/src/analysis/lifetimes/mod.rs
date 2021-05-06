//! This module contains the region analysis components implementing the `cavyc`
//! borrow checker. It is based directly on the outline in the [non-lexical
//! lifetimes
//! RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md) by
//! Matsakis et al.

// TODO
// + Collect liveness constraints

use core::fmt;
use std::collections::BTreeSet;

use bitvec::prelude::*;

use crate::{context::Context, mir::*, store::Store};
use crate::{store_type, util::FmtWith};

use super::dataflow::{DataflowCtx, DataflowRunner};

mod ascription;
mod liveness;
mod loan_scope;
mod regions;
mod util;

/// Main entry point for region inference and borrow checking
pub fn borrow_check(context: DataflowCtx) {
    let regions = regions::infer_regions(&context);
    println!("{:?}", regions);
}

// A map from lightweight lifetime variables to the regions they represent
store_type! { LifetimeStore : LtId -> Lifetime }

/// See [Named
/// lifetimes](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#layer-4-named-lifetimes):
/// this is exactly the data structure j
pub struct Lifetime {
    /// The "finite" points within the graph
    pts: Store<BlockId, BitVec>,
    /// The "points at infinity" in the caller. For now, we're making the
    /// simplifying assumption that there is a single such point; that is, that
    /// all function arguments and return values have the *same* lifetime. This
    /// bit is set if this lifetime extends to infinity.
    end: bool,
}

impl Lifetime {
    /// Add a single point to the lifetime
    pub fn insert(&mut self, pt: GraphPt) {
        let block = &mut self.pts[pt.blk];
        block.set(pt.stmt, true);
    }

    pub fn iter(&self) -> impl Iterator<Item = GraphPt> + '_ {
        self.pts
            .idx_enumerate()
            .map(move |(blk, stmts)| {
                stmts.iter().enumerate().filter_map(move |(stmt, bit)| {
                    if *bit {
                        Some(GraphPt { blk, stmt })
                    } else {
                        None
                    }
                })
            })
            .flatten()
    }

    pub fn contains(&self, pt: &GraphPt) -> bool {
        self.pts[pt.blk][pt.stmt]
    }
}

impl LifetimeStore {
    /// Construct an empty lifetime
    fn new_region(&mut self, block_sizes: &[usize]) -> LtId {
        let lifetime = Lifetime {
            pts: block_sizes.iter().map(|sz| bitvec![0; *sz]).collect(),
            end: false,
        };
        self.insert(lifetime)
    }

    /// Construct a lifetime that extends into the caller
    fn end_region(&mut self, block_sizes: &[usize]) -> LtId {
        let lifetime = Lifetime {
            pts: block_sizes.iter().map(|sz| bitvec![1; *sz]).collect(),
            end: true,
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

// === boilerplate impls ===

impl std::ops::Index<BlockId> for Lifetime {
    type Output = BitVec;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.pts[index]
    }
}

impl std::ops::IndexMut<BlockId> for Lifetime {
    fn index_mut(&mut self, index: BlockId) -> &mut Self::Output {
        &mut self.pts[index]
    }
}

impl fmt::Display for LtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", self.0)
    }
}
