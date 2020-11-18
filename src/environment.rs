use crate::circuit::Circuit;
use crate::values::Value;
use std::collections::HashMap;

pub struct Environment {
    values: HashMap<String, Value>,
    pub circuit: Circuit,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
            circuit: Circuit::new(),
        }
    }
}
