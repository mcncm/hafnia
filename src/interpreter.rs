use crate::environment::Environment;
use crate::parser::ParseError;
use crate::scanner::{ScanError, Scanner};
use std::fmt;

pub struct Interpreter {
    env: Environment,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Environment::new(),
        }
    }

    pub fn interpret(&mut self, _input: &str) -> Result<(), Vec<Box<dyn fmt::Display>>> {
        Ok(())
    }
}

pub struct CodeObject {
    // TODO
}
