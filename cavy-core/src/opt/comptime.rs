//! In Cavy, all classical values that can be computed at compile time are so
//! evalutated. We might call this "constant propagatation" or "compile-time
//! evaluation" in different places; here, the two will be synonymous.
//!
//! Which are the classical values that can be computed at compile time? In
//! short, any that are deterministic and not downstream of any measurement
//! operator. Since there is currently no primitive classical randomness in the
//! language, this means exactly that classical computation between the entry
//! point and the first linearization operator.
//!
//! NOTE This currently works under the assumption that there are no infinite
//! loops or recursion. It's one of the points of failure when that eventually
//! changes.

use std::collections::HashMap;

use crate::{
    context::Context,
    mir::{Graph, LocalId, Mir},
    values::Value,
};

/// Main entry point for compile-time evaluation. This takes the form of a Mir
/// optimization, which is currently a function taking a mutable reference to
/// the Mir. In the future, multiple optimizations may be handled by some common
/// framework, similar to the dataflow analyses.
///
/// For now, even *this* optimization is intraprocedural. That *must* change.
pub fn simplify(mir: &mut Mir, _ctx: &Context) {
    for gr in mir.graphs.iter_mut() {
        simpl_graph(gr);
    }
}

pub fn simpl_graph(gr: &mut Graph) {
    let interp = Interpreter::new();
}

struct Interpreter {
    env: HashMap<LocalId, Value>,
}

/// A graph-local interpreter for classical computations
impl Interpreter {
    fn new() -> Self {
        Self {
            env: HashMap::new(),
        }
    }
}
