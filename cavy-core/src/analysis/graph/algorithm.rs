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
        let (mut pre, mut post) = (vec![], vec![]);
        let pre_cb = |node| pre.push(node);
        let post_cb = |node| post.push(node);

        let mut walker = self.dfs_walker(self.root(), Box::new(pre_cb), Box::new(post_cb));
        // Exhaust the generator
        while walker().is_some() {}
        drop(walker);
        // Now our orders are full!
        (Preorder(pre), Postorder(post))
    }

    /*
    Ok, this was probably pretty irresponsible. I've *basically* just made a
    struct here, with methods and everything, but in a bizarre functional style
    full of `std::mem::replace` that no one will be able to read. This is
    officially the worst code in this project. I'm sorry, world.
    */

    /// Get a DFS iterator starting from any node
    fn dfs_from<'a>(&'a self, node: T) -> std::iter::FromFn<Box<dyn FnMut() -> Option<T> + 'a>>
    where
        T: 'a,
    {
        let mut walker = self.dfs_walker(node, Box::new(Option::from), Box::new(|_| None));
        let nodes = Box::new(move || walker().flatten());
        std::iter::from_fn(nodes)
    }

    /// Produce a DFS walker starting with a given node.
    fn dfs_walker<'a, U>(
        &'a self,
        // Starting node
        mut node: T,
        // Callback on entering a node
        mut pre: Box<dyn FnMut(T) -> U + 'a>,
        // Callback on exiting a node
        mut post: Box<dyn FnMut(T) -> U + 'a>,
    ) -> Box<dyn FnMut() -> Option<U> + 'a>
    where
        T: 'a,
        U: 'a,
    {
        let mut stack = vec![];
        let mut visited = HashSet::new(); // can optimize to BitVec
        let mut successors = [].iter();

        let dfs = move || {
            if visited.is_empty() {
                let fst = node.clone();
                successors = self.successors(&fst).iter();
                visited.insert(fst.clone());
                // "entering" callback with the first node
                Some(pre(fst.clone()))
            } else {
                match successors.find(|elem| !visited.contains(elem)) {
                    // There's an unvisited successor element
                    Some(succ) => {
                        // push a stack frame
                        let new_succs = self.successors(&node).iter();
                        let old_succs = std::mem::replace(&mut successors, new_succs);
                        stack.push((node.clone(), old_succs));
                        node = succ.clone();
                        visited.insert(succ.clone());
                        // "entering" callback with the new node
                        Some(pre(succ.clone()))
                    }
                    // No unvisited successor elements: back up the stack!
                    None => {
                        match stack.pop() {
                            Some((mut pred, mut old_succs)) => {
                                // Restore the previous stack frame
                                std::mem::swap(&mut successors, &mut old_succs);
                                std::mem::swap(&mut node, &mut pred);
                                // "leaving" callback with `node`
                                Some(post(pred))
                            }
                            // No more nodes to find
                            None => None,
                        }
                    }
                }
            }
        };

        Box::new(dfs)
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
