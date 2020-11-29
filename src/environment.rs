use crate::functions::builtins::BUILTINS;
use crate::{circuit::Qubit, functions::Func, values::Value};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

pub type Key = String;

/// The type of thing that an environment can hold; namely, a value or a
/// function.
/// TODO think of a better name than `Nameable`.
#[derive(Debug, Clone)]
pub enum Nameable {
    Value(Value),
    Func(Rc<dyn Func>),
}

/// Our environments are just linked lists, with the caveat that they are never empty.
#[derive(Default)]
struct EnvNode {
    pub values: HashMap<Key, Nameable>,
    pub controls: HashSet<Qubit>,
    pub enclosing: Option<Box<EnvNode>>,
}

impl EnvNode {
    pub fn ancestor_containing(&mut self, k: &str) -> Option<&mut EnvNode> {
        if self.values.contains_key(k) {
            Some(self)
        } else {
            match &mut self.enclosing {
                None => None,
                Some(node) => node.ancestor_containing(k),
            }
        }
    }

    pub fn insert(&mut self, k: Key, v: Nameable) -> Option<Nameable> {
        match self.ancestor_containing(&k) {
            None => self.values.insert(k, v),
            Some(node) => node.values.insert(k, v),
        }
    }

    /// This method may mutate `self` if we enforce linearity at
    /// "runtime," which is the approach currently taken.
    ///
    /// `moving` is a flag that indicates whether linear values should be moved
    /// out of the node when accessed.
    pub fn get(&mut self, k: &str, moving: bool) -> Option<Nameable> {
        self.ancestor_containing(k)
            .map(|node| node.get_inner(k, moving))
    }

    /// Get a value from this environment, assuming that it is *already known*
    /// to reside in this environment. This function shouldn’t be called
    /// externally, and is just an implementation detail of `get`.
    #[inline(always)]
    fn get_inner(&mut self, k: &str, moving: bool) -> Nameable {
        // This unwrap is safe because any ancestor is returned by
        // `ancestor_containing` is guaranteed to contain the value.
        let val = self.values.get(k).unwrap().clone();
        // NOTE When--and if--we move to fully static typechecking, this will
        // become unnecessary, and it will be removed.
        match val {
            Nameable::Func(_) => {}
            Nameable::Value(val) => {
                if moving & val.is_linear() {
                    self.values.remove(k);
                }
            }
        }
        val
    }
}

/// This struct is the public environment interface seen by the compiler.
///
/// The public field `moving` indicates whether accessed values are moved out of
/// the environment if they are linear. This stands to be removed in the future
/// if we replace dynamic linearity checking with a separate compiler pass.
pub struct Environment {
    // It is an invariant of this data structure that `store` never None.
    store: Option<Box<EnvNode>>,
    pub moving: bool,
}

impl Environment {
    /// Creates an empty environment
    pub fn new() -> Self {
        Self {
            store: Some(Box::new(EnvNode::default())),
            moving: true,
        }
    }

    /// Creates an environment with builtin functions included. This should only
    /// be called once, so I’m not very worried about the cost of cloning.
    /// Nevertheless, You might want to think about cleaner ways of doing this.
    pub fn base() -> Self {
        let mut env = Self::new();
        for (name, func) in BUILTINS.iter() {
            env.insert(name.to_string(), Nameable::Func(Rc::new(func.clone())));
        }
        env
    }

    //////////////////
    // Environments //
    //////////////////

    /// Push an environment onto the stack.
    pub fn open_scope(
        &mut self,
        values: Option<HashMap<Key, Nameable>>,
        controls: Option<HashSet<Qubit>>,
    ) {
        let values = values.unwrap_or_default();
        let controls = controls.unwrap_or_default();
        let new_store = Box::new(EnvNode {
            values,
            controls,
            enclosing: self.store.take(),
        });

        self.store = Some(new_store);
    }

    /// stack: there is always at least on environment, and `pop_env` simply
    /// returns `None` if only the root environment is left.
    pub fn close_scope(&mut self) {
        match std::mem::replace(&mut self.store, None) {
            None => unreachable!(),
            Some(mut node) => {
                self.store = node.enclosing.take();
            }
        }
    }

    pub fn insert(&mut self, k: Key, v: Nameable) -> Option<Nameable> {
        self.store.as_mut().unwrap().insert(k, v)
    }

    /// Note that this method may mutate `self` if we enforce linearity at
    /// "runtime."
    pub fn get(&mut self, k: &str) -> Option<Nameable> {
        self.store.as_mut().unwrap().get(k, self.moving)
    }

    /// Add a control in the current scope
    pub fn insert_control(&mut self, qubit: Qubit) -> bool {
        self.store.as_mut().unwrap().controls.insert(qubit)
    }

    // this method shouldn’t be necessary; controls should be associated with a
    // scope, and disappear when it ends.
    pub fn remove_control(&mut self, qubit: Qubit) -> bool {
        self.store.as_mut().unwrap().controls.remove(&qubit)
    }

    pub fn controls(&self) -> &HashSet<Qubit> {
        &self.store.as_ref().unwrap().controls
    }
}
