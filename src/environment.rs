use crate::circuit::Circuit;
use crate::values::Value;
use std::collections::HashMap;

type Key = String;

#[derive(Default)]
pub struct Environment {
    pub values: HashMap<Key, Value>,
    pub circuit: Circuit,
    enclosing: Option<Box<Self>>,
}

impl Environment {
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
