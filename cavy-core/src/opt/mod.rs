//! This module handles the mir-level "optimizations", which are understood as
//! anything that mutates the Mir.

use crate::{context::Context, mir::Mir, session::Config};
mod comptime;

/// Type of an optimization routine
type OptFn = dyn Fn(&mut Mir, &Context);

/// Type of a predicate guarding the application of an optimization
type GuardFn = dyn Fn(&Config) -> bool;

/// This static array holds the optimizations that may be applied, together with
/// the conditions under which they are.
#[rustfmt::skip]
const OPTS: [(&OptFn, &GuardFn); 1] = [
    // Compile-time evaluation: should be applied unconditionally.
    (&comptime::propagate_consts, &|conf| conf.opt.comptime)
];

/// Decide whether to apply an optimization based on the attached guard function
fn accept_opt<'f>(opt: &(&'f OptFn, &'f GuardFn), ctx: &Context) -> Option<&'f OptFn> {
    let cond = opt.1;
    if cond(ctx.conf) {
        Some(opt.0)
    } else {
        None
    }
}

/// Main entry point for the `opt` module
pub fn optimize(mir: &mut Mir, ctx: &Context) {
    for opt in OPTS.iter().filter_map(|opt| accept_opt(opt, ctx)) {
        opt(mir, ctx)
    }
}
