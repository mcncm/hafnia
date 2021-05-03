//! This module contains the region analysis components implementing the `cavyc`
//! borrow checker. It is based directly on the outline in the [non-lexical
//! lifetimes
//! RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md) by
//! Matsakis et al.

// TODO
// + Collect liveness constraints

use std::collections::BTreeSet;

use crate::store_type;
use crate::{context::Context, mir::*};

mod liveness;

pub struct LoanData();

// A map from lightweight "lifetime" variables to the regions they represent
store_type! { LifetimeStore : Lt -> Lifetime }

struct Lifetime {
    locs: BTreeSet<GraphLoc>,
}

/// The constraint representation described in `#Lifetime inference constraints`
/// of the NLL RFC.
struct Constraint {
    long: Lt,
    shrt: Lt,
    loc: GraphLoc,
}

struct BorrowChecker {
    regions: LifetimeStore,
    constraints: Vec<Constraint>,
}

/// Precomputed data about the graph
struct GraphData<'a> {
    gr: &'a Graph,
    rpo: Vec<BlockId>,
}

impl Place {
    /// The minimum path length for a subpath `Place` to be a supporting prefix
    fn supporting_prefix_len(&self, ctx: &Context) -> usize {
        let mut len = self.path.len();
        for elem in self.path.iter().rev() {
            match elem {
                Proj::Field(_) => {}
                Proj::Deref => {}
            }
        }
        todo!()
    }
}
