use std::vec::Vec;

use crate::parser;
use crate::environment::Environment;

pub struct Interpreter {
    env: Environment,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {
            env: Environment::new(),
        }
    }

    pub fn interpret(&mut self, input: &str) -> () {
        println!("Your input: {}", input)
    }
}

pub struct CodeObject {
    // TODO
}
