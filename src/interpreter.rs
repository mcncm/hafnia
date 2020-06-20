use crate::environment::Environment;
use crate::errors::Error;

pub struct Interpreter {
    env: Environment,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Environment::new(),
        }
    }

    pub fn interpret(&mut self, input: &str) -> Result<(), Error> {
        println!("Your input: {}", input);
        Ok(())
    }
}

pub struct CodeObject {
    // TODO
}
