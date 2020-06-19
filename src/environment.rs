use std::collections::HashMap;

// The unsigned type that we will wrap as a natural number or qubit.
type Unsigned = u32;

/// Value type: variants correspond to the types of the object language.
pub enum Value {
    Nat(Unsigned),
    Bool(bool),
    Qubit(usize),
}

pub struct Environment {
    values: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            values: HashMap::new(),
        }
    }
}
