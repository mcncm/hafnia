use crate::{
    circuit::Qubit,
    values::{Func, Value},
};
use std::collections::{HashMap, HashSet};

type Key = String;

/// The type of thing that an environment can hold; namely, a value or a
/// function.
/// TODO think of a better name than `Nameable`.
pub enum Nameable {
    Value(Value),
    Func(Func),
}

#[derive(Default)]
pub struct Environment<'a> {
    pub values: HashMap<Key, Nameable>,
    pub controls: HashSet<Qubit>,
    enclosing: Option<&'a Self>,
}

impl<'a> Environment<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, k: Key, v: Nameable) -> Option<Nameable> {
        self.values.insert(k, v)
    }

    /// Note that this method may mutate `self` if we enforce linearity at
    /// "runtime."
    pub fn get(&mut self, k: &str) -> Option<&Nameable> {
        self.values.get(k)
    }
}
