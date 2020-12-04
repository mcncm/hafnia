use crate::backend::target::{Qasm, TargetSerializable};
use crate::functions::builtins::BUILTINS;
use crate::{circuit::Qubit, functions::Func, values::Value};
use serde::{self, Deserialize, Serialize};
use std::{
    cell::RefCell,
    collections::{hash_set::Union, HashMap, HashSet},
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

/// Essentially an alias for Option that's supposed to represent something that
/// may or may not have been moved. It’s not a true alias, though, because it
/// should really be a different type to avoid confusion within the nest of
/// `get` methods that return Options.
pub enum Moveable<T> {
    There(T),
    Moved,
}

impl<T> Default for Moveable<T> {
    fn default() -> Self {
        Moveable::Moved
    }
}

impl<T> Moveable<T> {
    pub fn take(&mut self) -> Self {
        std::mem::take(self)
    }
}

impl<T> Into<Option<T>> for Moveable<T> {
    fn into(self) -> Option<T> {
        match self {
            Moveable::There(v) => Some(v),
            Moveable::Moved => None,
        }
    }
}

/// Our environments are just linked lists, with the caveat that they are never empty.
#[derive(Default)]
struct EnvNode {
    pub values: HashMap<Key, Moveable<Nameable>>,
    pub enclosing: Option<Box<EnvNode>>,
    controls: HashSet<Qubit>,
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
        use Moveable::*;
        let v = There(v);
        let prev = match self.ancestor_containing(&k) {
            None => self.values.insert(k, v),
            Some(node) => node.values.insert(k, v),
        };
        match prev {
            Some(There(val)) => Some(val),
            _ => None,
        }
    }

    /// This method may mutate `self` if we enforce linearity at
    /// "runtime," which is the approach currently taken.
    ///
    /// `moving` is a flag that indicates whether linear values should be moved
    /// out of the node when accessed.
    pub fn get(&mut self, k: &str, moving: bool) -> Option<Moveable<Nameable>> {
        self.ancestor_containing(k)
            .map(|node| node.get_inner(k, moving))
    }

    /// Get a value from this environment, assuming that it is *already known*
    /// to reside in this environment. This function shouldn’t be called
    /// externally, and is just an implementation detail of `get`.
    #[inline(always)]
    fn get_inner(&mut self, k: &str, moving: bool) -> Moveable<Nameable> {
        use Moveable::*;
        use Nameable::*;
        // This unwrap is safe because any ancestor returned by
        // `ancestor_containing` is guaranteed to contain the key.
        let val = self.values.get_mut(k).unwrap();
        match val {
            There(Value(v)) if moving & v.is_linear() => val.take(),
            There(x) => There(x.clone()),
            Moved => Moved,
        }
    }

    /// Get a reference to all the controlled qubits in this scope
    ///
    /// TODO Figure out how to return a Union<&Qubit, _> instead of allocating.
    /// What is the second type parameter?
    pub fn all_controls(&self) -> HashSet<Qubit> {
        match &self.enclosing {
            Some(node) => node
                .all_controls()
                .union(&self.controls)
                .copied() // Awkward copy that shouldn’t really be necessary
                .collect(),
            None => self.controls.clone(),
        }
    }

    fn insert_control(&mut self, qubit: Qubit) -> bool {
        self.controls.insert(qubit)
    }

    fn remove_control(&mut self, qubit: &Qubit) -> bool {
        self.controls.remove(qubit)
    }
}

/// We want to be able to serialize environments so we can dump the variable
/// bindings in the base environment when we write the object code; however,
/// we probably won't care about deserializing an environment node.
impl Serialize for EnvNode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // We'll filter out just the things that we actually care to serialize;
        // namely, values that haven't been moved.
        let mut table = HashMap::new();
        for (key, val) in self.values.iter() {
            if let Moveable::There(Nameable::Value(val)) = val {
                table.insert(key, val);
            }
        }
        table.serialize(serializer)
    }
}

/// This implementation has to be here because `EnvNode` is not `pub`.
impl TargetSerializable<Qasm> for EnvNode {
    fn to_target(&self) -> Qasm {
        let json = serde_json::to_value(self).unwrap();
        Qasm(json.to_string())
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
        let values = values
            .unwrap_or_default()
            .into_iter()
            .map(|(key, value)| (key, Moveable::There(value)))
            .collect();
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
    pub fn get(&mut self, k: &str) -> Option<Moveable<Nameable>> {
        self.store.as_mut().unwrap().get(k, self.moving)
    }

    /// Add a control in the current scope
    pub fn insert_control(&mut self, qubit: Qubit) -> bool {
        self.store.as_mut().unwrap().insert_control(qubit)
    }

    // this method shouldn’t be necessary; controls should be associated with a
    // scope, and disappear when it ends.
    pub fn remove_control(&mut self, qubit: Qubit) -> bool {
        self.store.as_mut().unwrap().remove_control(&qubit)
    }

    pub fn controls(&self) -> HashSet<Qubit> {
        self.store.as_ref().unwrap().all_controls()
    }
}

/// This implementation has to be here becuase `store` is not a `pub` field.
impl TargetSerializable<Qasm> for Environment {
    fn to_target(&self) -> Qasm {
        Qasm(self.store.as_ref().unwrap().to_target().0)
    }
}
