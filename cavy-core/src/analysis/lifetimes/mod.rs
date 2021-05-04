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

use super::dataflow::{DataflowCtx, DataflowRunner};

/// Print some analysis results to the console for debugging
macro_rules! ltdbg {
    ($result:ident, $context:ident) => {
        if cfg!(debug_assertions) {
            let name: &'static str = stringify!($result);
            let name = name.to_uppercase();
            println!(
                "{}:\n{}",
                name,
                crate::util::FmtWith::fmt_with(&$result, &$context)
            );
        }
    };
}

pub(crate) use ltdbg;

mod ascription;
mod liveness;
mod regions;
mod util;

// A map from lightweight "lifetime" variables to the regions they represent
store_type! { LifetimeStore : LtId -> Lifetime }

pub struct Lifetime {
    locs: BTreeSet<GraphLoc>,
}

pub fn borrow_check(context: DataflowCtx) {
    let lifetimes = regions::infer_regions(&context);
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
