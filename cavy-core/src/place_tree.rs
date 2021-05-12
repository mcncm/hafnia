//! Data structures for `Place`wise addressing
//!
//! I'm not super happy about this data structure. I'm using it in three places
//! (worse than that, something *like* it; I'm replicating work even though this
//! is generic) . It's ugly, and probably ineffecient, and it's basically
//! programming Python. There are definitely cleverer data structures I could
//! use. But this gets the job done.
//!
//! FIXME: this should be used in `ascriptions.rs` and `linearity.rs` as well,
//! as they do the exact same thing, but I don't have the time to refactor them
//! for the generic implementation right now.

use std::iter::FromIterator;

use crate::{
    mir::{LocalId, Place, Proj},
    store::Store,
};

/// Ok, this is a bit of an odd tree, but it might actually be the most efficient in
/// practice, noting that very few variables will have wide-branching `Place` trees.

/// A generic store for place-indexed data, backed by a `LocalId` store of
/// trees.
pub struct PlaceStore<T> {
    store: Store<LocalId, PlaceNode<T>>,
}

impl<T> PlaceStore<T> {
    pub fn new() -> Self {
        Self {
            store: Store::new(),
        }
    }

    /// Insert a value at a place and return the previous value, if any
    pub fn insert(&mut self, place: &Place, val: T) -> Option<T> {
        let node = self.node_creating(place);
        node.this.replace(val)
    }

    pub fn get(&self, place: &Place) -> Option<&T> {
        self.node_at(place).and_then(|node| node.this.as_ref())
    }

    pub fn get_mut(&mut self, place: &Place) -> Option<&mut T> {
        self.node_at_mut(place).and_then(|node| node.this.as_mut())
    }

    /// Iterate over the `Place` tree in postorder from a root.
    pub fn iter_post(&self, local: LocalId) -> impl Iterator<Item = &T> + '_ {
        let node = &self.store[local];
        node.iter_post()
    }

    /// Iterate over the `Place` tree in postorder, from a starting path.
    pub fn iter_post_from(&mut self, place: &Place) -> impl Iterator<Item = &T> + '_ {
        self.node_at(place)
            .map(|node| node.iter_post())
            .into_iter()
            .flatten()
    }

    fn node_at(&self, place: &Place) -> Option<&PlaceNode<T>> {
        let mut node = Some(&self.store[place.root]);
        let mut projections = place.path.iter();
        while let Some(sub) = node {
            node = match projections.next() {
                Some(Proj::Field(n)) => sub.slots[*n].as_ref(),
                Some(Proj::Deref) => sub.slots[0].as_ref(),
                None => None,
            };
        }
        node
    }

    // Hm, ok, this is why people want to write generically over mutability.

    fn node_at_mut(&mut self, place: &Place) -> Option<&mut PlaceNode<T>> {
        let mut node = Some(&mut self.store[place.root]);
        let mut projections = place.path.iter();
        while let Some(sub) = node {
            node = match projections.next() {
                Some(Proj::Field(n)) => (&mut sub.slots[*n]).as_mut(),
                Some(Proj::Deref) => (&mut sub.slots[0]).as_mut(),
                None => None,
            };
        }
        node
    }

    /// Get a node at a `Place`, possibly creating nodes along the way.
    fn node_creating(&mut self, place: &Place) -> &mut PlaceNode<T> {
        // I just noticed something. This "Store" type is a leaky abstraction. I
        // have to carry around all this knowledge about its
        // implementation everywhere I go.
        let diff = (1 + <u32>::from(place.root) as usize).saturating_sub(self.store.len());
        self.store
            .extend(std::iter::repeat_with(|| PlaceNode::default()).take(diff));

        let mut node = &mut self.store[place.root];
        for elem in &place.path {
            let slot = match elem {
                Proj::Field(n) => {
                    let diff = 1 + n.saturating_sub(node.slots.len());
                    node.slots
                        .extend(std::iter::repeat_with(|| None).take(diff));
                    *n
                }
                Proj::Deref => {
                    if node.slots.is_empty() {
                        node.slots.push(None);
                    }
                    0
                }
            };
            node = node.slots[slot].get_or_insert_with(|| PlaceNode::default());
        }
        node
    }
}

impl<T> FromIterator<PlaceNode<T>> for PlaceStore<T> {
    fn from_iter<I: IntoIterator<Item = PlaceNode<T>>>(iter: I) -> Self {
        Self {
            store: iter.into_iter().collect(),
        }
    }
}

/// A node in a `Place` tree.
#[derive(Debug)]
pub struct PlaceNode<T> {
    /// Items at this `Place`
    pub this: Option<T>,
    /// Items at deeper paths
    pub slots: Vec<Option<PlaceNode<T>>>,
}

impl<T> PlaceNode<T> {
    fn iter_post<'a>(&'a self) -> PlaceTreePost<'a, T> {
        PlaceTreePost {
            stack: vec![],
            node: self,
            slots: self.slots.iter(),
            end: false,
        }
    }
}

impl<T> Default for PlaceNode<T> {
    fn default() -> Self {
        Self {
            this: None,
            slots: vec![],
        }
    }
}

/// A postorder iterator on a `PlaceTree`
pub struct PlaceTreePost<'a, T> {
    stack: Vec<(&'a PlaceNode<T>, std::slice::Iter<'a, Option<PlaceNode<T>>>)>,
    node: &'a PlaceNode<T>,
    slots: std::slice::Iter<'a, Option<PlaceNode<T>>>,
    // Hack for last-node edge case. There's definitely a "good" pattern for
    // this that isn't as much of a hack, but too bad.
    end: bool,
}

impl<'a, T> PlaceTreePost<'a, T> {
    /// Go back down the stack/up the tree.
    fn pop(&mut self) {
        if let Some((prev_node, prev_slots)) = self.stack.pop() {
            self.node = prev_node;
            self.slots = prev_slots;
        } else {
            self.end = true;
        }
    }
}

impl<'a, T> Iterator for PlaceTreePost<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.end {
            return None;
        }

        // More child nodes: go down
        if let Some(Some(sub)) = self.slots.find(|elem| elem.is_some()) {
            let sub_slots = sub.slots.iter();
            let this_node = std::mem::replace(&mut self.node, sub);
            let this_slots = std::mem::replace(&mut self.slots, sub_slots);
            self.stack.push((this_node, this_slots));
            self.next()
        // No more child nodes
        } else if let val @ Some(_) = self.node.this.as_ref() {
            self.pop();
            val
        } else {
            self.pop();
            self.next()
        }
    }
}
