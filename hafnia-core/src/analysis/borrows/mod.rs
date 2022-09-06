//! This module contains the region analysis components implementing the `hafniac`
//! borrow checker. It is based directly on the outline in the [non-lexical
//! lifetimes
//! RFC](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md) by
//! Matsakis et al.

// TODO
// + Collect liveness constraints

use core::fmt;
use std::collections::BTreeSet;

use bitvec::prelude::*;

use crate::{hafnia_errors::ErrorBuf, context::Context, mir::*, store::Store};
use crate::{store_type, util::FmtWith};

use super::{
    controls::ControlPlaces,
    dataflow::{DataflowCtx, DataflowRunner},
};

mod ascription;
mod borrow_check;
mod liveness;
mod loan_scope;
pub mod regions;
mod util;

/// Main entry point for region inference and borrow checking
pub fn check(context: DataflowCtx, controls: &ControlPlaces, errs: &mut ErrorBuf) {
    let regions = regions::infer_regions(&context, controls);

    #[cfg(debug_assertions)]
    {
        if context.ctx.conf.phase_config.last_phase == crate::session::Phase::Analysis {
            println!("{:?}", regions);
        }
    }

    let scopes = loan_scope::loan_scopes(&regions, &context);

    if context.ctx.conf.phase_config.last_phase == crate::session::Phase::Analysis {
        println!("LOAN SCOPES");
        println!("{}\n\n", scopes.fmt_with(&context));
    }

    borrow_check::borrow_check(&regions, &scopes, &context, errs);
}
