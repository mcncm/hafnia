use crate::functions::builtins::BUILTINS;
use crate::target::{qasm::Qasm, IntoTarget, Target};
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
    // Uniqueness of the elements must be enforced by the user of this data
    // structure. Note that we won't ever need to remove controls by value: they
    // are only removed by going out of scope!
    controls: Vec<Qubit>,
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

    /// Get a reference to all the controlled qubits in this scope.
    pub fn all_controls(&self) -> Box<dyn Iterator<Item = &Qubit> + '_> {
        use std::iter;
        let controls = self.controls.iter().chain(match &self.enclosing {
            Some(node) => node.controls.iter(),
            None => [].iter(),
        });
        Box::new(controls)
    }

    fn insert_control(&mut self, qubit: Qubit) {
        self.controls.push(qubit)
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
impl IntoTarget<Qasm> for EnvNode {
    fn into_target(&self, _target: &Qasm) -> String {
        let json = serde_json::to_value(self).unwrap();
        json.to_string()
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
    pub fn open_scope(&mut self, values: Option<HashMap<Key, Nameable>>, controls: Vec<Qubit>) {
        let values = values
            .unwrap_or_default()
            .into_iter()
            .map(|(key, value)| (key, Moveable::There(value)))
            .collect();
        // We must put the bindings directly in the new node, because they might
        // shadow outer bindings! This is essential for `let` and `for` to work
        // correctly.
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
    pub fn insert_control(&mut self, qubit: Qubit) {
        self.store.as_mut().unwrap().insert_control(qubit)
    }

    pub fn controls(&self) -> Box<dyn Iterator<Item = Qubit>> {
        let controls: Vec<Qubit> = self
            .store
            .as_ref()
            .unwrap()
            .all_controls()
            // FIXME We are, for now, going to punt on the question of lifetimes
            // of controls. Indeed, this data only lives as long as the
            // innermost scope. To return only *references* to the controls, we
            // would need to prove that nothing the interpreter does with them
            // outlives that scope. To save that hassle, for the time being,
            // we'll simply clone this iterator.
            .cloned()
            .collect();
        Box::new(controls.into_iter())
    }
}

/// This implementation has to be here becuase `store` is not a `pub` field.
impl IntoTarget<Qasm> for Environment {
    fn into_target(&self, target: &Qasm) -> String {
        self.store.as_ref().unwrap().into_target(target)
    }
}
