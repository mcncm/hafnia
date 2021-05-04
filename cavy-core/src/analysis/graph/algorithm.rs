//! Some useful graph algorithms: computing traversal orders, reachability, etc.

use std::collections::HashSet;
use std::hash::Hash;

use crate::mir::{BlockId, Graph};

/// Make wrapper types for graph traversal orders
macro_rules! traversal_orders {
    ($($name:ident),*) => {
        $(
            #[derive(Clone)]
            pub struct $name<T>(Vec<T>);

            impl<T> $name<T> {
                pub fn iter(&self) -> impl Iterator<Item = &T> + DoubleEndedIterator {
                    self.0.iter()
                }
            }

            impl<T> From<$name<T>> for Vec<T> {
                fn from(p: $name<T>) -> Self {
                    p.0
                }
            }
        )*
    };
}

traversal_orders! { Preorder, Postorder }

pub fn traversals(gr: &Graph) -> (Preorder<BlockId>, Postorder<BlockId>) {
    gr.traversals()
}

/// A (currently uniquely) rooted directed graph
trait Digraph<T>
where
    T: Clone + Hash + PartialEq + Eq,
    Self: Sized,
{
    fn root(&self) -> T;

    fn successors(&self, node: &T) -> &[T];

    /// Compute pre- and post-orders. At first, we'll assume that the entire
    /// graph is reachable from the root.
    fn traversals(&self) -> (Preorder<T>, Postorder<T>) {
        let walker = DfsWalker {
            visited: HashSet::new(), // could optimize to BitVec
            pre: vec![],
            post: vec![],
            gr: self,
        };
        walker.traverse()
    }
}

impl Digraph<BlockId> for Graph {
    fn root(&self) -> BlockId {
        self.entry_block
    }

    fn successors(&self, node: &BlockId) -> &[BlockId] {
        self[*node].successors()
    }
}

struct DfsWalker<'a, T, G: Digraph<T>>
where
    T: Clone + Hash + PartialEq + Eq,
{
    pre: Vec<T>,
    post: Vec<T>,
    visited: HashSet<T>,
    gr: &'a G,
}

impl<'a, T, G: Digraph<T>> DfsWalker<'a, T, G>
where
    T: Clone + Hash + PartialEq + Eq,
{
    fn traverse(mut self) -> (Preorder<T>, Postorder<T>) {
        let node = self.gr.root();
        self.dfs(node);
        (Preorder(self.pre), Postorder(self.post))
    }

    fn dfs(&mut self, node: T) {
        self.visited.insert(node.clone());
        self.pre.push(node.clone());
        for succ in self.gr.successors(&node).iter().cloned() {
            if !self.visited.contains(&succ) {
                self.dfs(succ);
            }
        }
        self.post.push(node);
    }
}
