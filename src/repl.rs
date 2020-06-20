use std::io::{self, Write};

use crate::backend::Backend;
use crate::errors;
use crate::interpreter::Interpreter;
use crate::sys;

const UNICODE_PROMPT: &'static str = "ψ⟩ ";
const ASCII_PROMPT: &'static str = "> ";
const WELCOME: &'static str = "Welcome to the alpha version of cavy-rs!";
const GOODBYE: &'static str = "Thanks for hacking with us!";
const HELP: &'static str = "Enter ':h' for help, or ':q' to quit.";

pub struct Repl {
    interpreter: Interpreter,
    backend: Box<dyn Backend>,
    flags: sys::Flags,
}

impl Repl {
    pub fn new(backend: Box<dyn Backend>, flags: sys::Flags) -> Repl {
        Repl {
            interpreter: Interpreter::new(),
            backend: backend,
            flags: flags,
        }
    }

    pub fn run(&mut self) -> () {
        self.greet();
        loop {
            let input = self.get_input();
            match input.as_str() {
                ":q" => {
                    break;
                }
                ":h" => {
                    self.help();
                }
                ":w" => {
                    self.wheek();
                }
                s => {
                    self.interpreter.interpret(s).unwrap_or_else(|err| {
                        self.handle_error(err);
                    });
                }
            }
        }
        self.farewell();
    }

    fn handle_error(&self, err: errors::Error) -> () {
        println!("Error: {:?}", err);
    }

    fn greet(&self) -> () {
        println!("{}", WELCOME);
        if self.flags.debug {
            println!("This interpreter is running in DEBUG mode.");
        }
        self.help();
    }

    fn farewell(&self) -> () {
        println!("{}", GOODBYE);
    }

    fn help(&self) -> () {
        println!("{}", HELP);
    }

    // An undocumented behavior of the repl
    fn wheek(&self) -> () {
        println!("Wheek!");
    }

    fn get_input(&self) -> String {
        print!("{}", UNICODE_PROMPT);
        io::stdout().flush().expect("Failed to flush stdout.");

        let mut input = String::new();
        io::stdin()
            .read_line(&mut input)
            .expect("Failed to read input.");

        input.trim().to_owned()
    }
}
