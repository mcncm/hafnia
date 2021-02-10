//! An analysis pass to compute the functions called by a single function. This
//!
//! is used mostly for two purposes: to prune disconnected functions from the
//! codegen phase, and to detect (mutual) recursion, which may be illegal,
//! depending on an architecture flag.
//!
//! It may be possible to do a more sophisticated analysis with some fancy
//! interprocedural symbolic execution to show that the recursion always
//! terminates after a finite number of cycles.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::mir::Graph;
use crate::source::Span;
use crate::{ast::FnId, mir::BlockKind};
use crate::{cavy_errors::ErrorBuf, context::Context, store::Store};

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
        match block {
            BlockKind::Call { callee, span, .. } => {
                state.insert(*callee, *span);
            }
            _ => {}
        }
    }
}

/// A graph of call sites for the entire MIR
type CallGraph = Store<FnId, CallSites>;

/// A check on the results of the call graph analysis that verifies the absence
/// of recursion.
pub fn check_recursion(errs: &mut ErrorBuf, call_sites: &CallGraph) {
    let components = SCCFinder::new(call_sites).components();
    for component in components {
        if component.len() == 1 {
            errs.push(errors::SimpleRecursion {
                span: component[0].1,
            });
        } else {
            // FIXME We should say something more interesting in these errors,
            // and be able to show the whole cycle.
            errs.push(errors::MutualRecursion {
                span: component[0].1,
            });
        }
    }
}

/// This data structure is an implementation detail of the SSCFinder to get a
/// stack with O(1) lookup and satellite data. We can simly use a `BTreeSet`
/// once [map_first_last](https://github.com/rust-lang/rust/issues/62924)
/// stabilizes.
struct StackMap<K: Hash + Eq + Clone, V> {
    stack: Vec<K>,
    map: HashMap<K, V>,
}

impl<K: Hash + Eq + Clone, V> StackMap<K, V> {
    fn new() -> Self {
        Self {
            stack: vec![],
            map: HashMap::new(),
        }
    }

    fn push(&mut self, k: K, v: V) {
        self.stack.push(k.clone());
        self.map.insert(k, v);
    }

    fn pop(&mut self) -> Option<(K, V)> {
        let elem = self.stack.pop();
        if let Some(elem) = elem {
            // remove from the map and retrieve the satellite data
            let data = self.map.remove(&elem).unwrap();
            Some((elem, data))
        } else {
            None
        }
    }

    fn contains(&self, k: &K) -> bool {
        self.map.contains_key(k)
    }

    fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        self.map.get_mut(k)
    }
}

/// Finds strongly-connected components of a call graph. The implementation is
/// derived from the pseudocode
/// [here](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm#The_algorithm_in_pseudocode).
/// Note that the comments here are the same as in that pseudocode, to make it
/// easier to compare them. It has been modified in two ways: single-node
/// components are only included in the output if they have a self-loop (simple
/// recursion), and we add some satellite data to the nodes, which takes a
/// little bookkeeping when components are emitted.
struct SCCFinder<'cg> {
    next_index: usize,
    stack: StackMap<FnId, Span>,
    // Can these be made into `Store`s? Probably.
    indices: HashMap<FnId, usize>,
    lowlinks: HashMap<FnId, usize>,
    call_graph: &'cg CallGraph,
    components: Vec<Vec<(FnId, Span)>>,
}

impl<'cg> SCCFinder<'cg> {
    fn new(call_graph: &'cg CallGraph) -> Self {
        let indices = HashMap::with_capacity(call_graph.len());
        let lowlinks = HashMap::with_capacity(call_graph.len());
        Self {
            next_index: 0,
            stack: StackMap::new(),
            indices,
            lowlinks,
            call_graph,
            components: Vec::new(),
        }
    }

    /// Compute all the cycles in the call graph. This is a mildly adapted
    /// version of Tarjan's strongly-connected components algorithm.
    fn components(mut self) -> Vec<Vec<(FnId, Span)>> {
        for (node, edges) in self.call_graph.idx_enumerate() {
            if !self.indices.contains_key(&node) {
                self.strong_connect(&node, Span::default(), edges);
            }
        }

        self.components
    }

    fn strong_connect(&mut self, node: &FnId, span: Span, edges: &'cg HashMap<FnId, Span>) {
        use std::cmp;

        self.indices.insert(*node, self.next_index);
        self.lowlinks.insert(*node, self.next_index);
        self.next_index += 1;
        self.stack.push(*node, span);

        for (succ, span) in edges {
            let min: usize;
            if !self.indices.contains_key(succ) {
                let edges = &self.call_graph[*succ];
                // Successor has not yet been visited; recurse on it
                self.strong_connect(succ, *span, edges);
                min = cmp::min(self.lowlinks[node], self.lowlinks[succ]);
                self.lowlinks.insert(*node, min);
            } else if self.stack.contains(succ) {
                // Successor `succ` is in stack and hence in the current SCC. If
                // `succ` is not on stack, then (`node`, `succ`) is an edge
                // pointing to an SCC already found and must be ignored.
                min = cmp::min(self.lowlinks[node], self.indices[succ]);
                self.lowlinks.insert(*node, min);
                // mcncm - In this addition, we modify the span of the
                // just-encountered node to reflect the point it was
                // encountered.
                let orig_span = self.stack.get_mut(succ).unwrap();
                *orig_span = *span;
            }
        }

        // If v is a root node, pop the stack and generate an SCC
        if self.lowlinks[node] == self.indices[node] {
            let mut component = Vec::new();
            loop {
                let other = self.stack.pop().unwrap();
                component.push(other);
                if &other.0 == node {
                    break;
                }
            }

            // mcncm - One last thing: a one-element component is not guaranteed
            // to have a self-loop, so we need to check explicitly.
            if component.len() == 1 {
                let elem = component[0].0;
                if !self.call_graph[elem].contains_key(&elem) {
                    return;
                }
            }

            self.components.push(component);
        }
    }
}

mod errors {
    use crate::context::{Context, CtxDisplay, SymbolId};
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    pub struct SimpleRecursion {
        #[msg = "function is recursive"]
        /// The location of the function call
        pub span: Span,
    }

    // TODO This error message should be able to report the whole cycle.
    #[derive(Diagnostic)]
    pub struct MutualRecursion {
        #[msg = "detected a mutually-recursive cycle"]
        /// The location of the function call
        pub span: Span,
    }
}
