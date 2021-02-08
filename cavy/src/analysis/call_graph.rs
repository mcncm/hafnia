//! An analysis pass to compute the functions called by a single function. This
//! is used mostly for two purposes: to prune disconnected functions from the
//! codegen phase, and to detect (mutual) recursion, which may be illegal,
//! depending on an architecture flag.
//!
//! It may be possible to do a more sophisticated analysis with some fancy
//! interprocedural symbolic execution to show that the recursion always
//! terminates after a finite number of cycles.

use std::collections::HashMap;

use crate::context::Context;
use crate::mir::Graph;
use crate::source::Span;
use crate::{ast::FnId, mir::BlockKind};

use super::common::{Analysis, Forward, Lattice};

/// The state for this summary analysis is the collection of call sites found in
/// the control-flow graph. For simplicity, we'll only track at most one such
/// site, but in the future we might like to keep track of all of them.
pub type CallSites = HashMap<FnId, Span>;

/// Note that this uses a *lot* more space than it needs to! We could really use
/// two bits for each local, for a whole procedure. (...That must be what this
/// gen-kill thing is all about.)
pub struct CallGraphAnalysis {}

impl Analysis<'_, '_> for CallGraphAnalysis {
    type Direction = Forward;
    type Domain = CallSites;

    /// Do absolutely nothing: calls appear in basic block tails, so these are
    /// all we care about.
    fn trans_stmt(&self, _state: &mut Self::Domain, _stmt: &crate::mir::Stmt) {}

    fn trans_block(&self, state: &mut Self::Domain, block: &BlockKind) {
        println!("hello out there!");
        match block {
            BlockKind::Call { callee, span, .. } => {
                state.insert(*callee, *span);
            }
            _ => {}
        }
    }
}
