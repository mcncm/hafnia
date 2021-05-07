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

use crate::{cavy_errors::ErrorBuf, context::Context, mir::*, store::Store};
use crate::{store_type, util::FmtWith};

use super::dataflow::{DataflowCtx, DataflowRunner};

mod ascription;
mod borrow_check;
mod liveness;
mod loan_scope;
mod regions;
mod util;

/// Main entry point for region inference and borrow checking
pub fn check(context: DataflowCtx, errs: &mut ErrorBuf) {
    let regions = regions::infer_regions(&context);
    println!("{:?}", regions);

    let scopes = loan_scope::loan_scopes(&regions, &context);
    println!("LOAN SCOPES");
    println!("{}\n\n", scopes.fmt_with(&context));
}

// Put me somewhere else; probably in `regions.rs`
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
