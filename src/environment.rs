use crate::{circuit::Qubit, values::Value};
use std::collections::{HashMap, HashSet};

type Key = String;

#[derive(Default)]
pub struct Environment<'a> {
    pub values: HashMap<Key, Value>,
    pub controls: HashSet<Qubit>,
    enclosing: Option<&'a Self>,
}

impl<'a> Environment<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, k: Key, v: Value) -> Option<Value> {
        self.values.insert(k, v)
    }

    /// Note that this method may mutate `self` if we enforce linearity at
    /// "runtime."
    pub fn get(&mut self, k: &str) -> Option<&Value> {
        self.values.get(k)
    }
}
