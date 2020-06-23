use crate::backend::Backend;
use crate::errors;
use crate::interpreter::Interpreter;
use crate::parser::Parser;
use crate::scanner::{Scanner, SourceObject};
use crate::sys;
use std::fmt::Display;
use std::io::{self, Write};

const UNICODE_PROMPT: &str = "ψ⟩ ";
const ASCII_PROMPT: &str = "> ";
const WELCOME: &str = "Welcome to the alpha version of cavy-rs!";
const GOODBYE: &str = "Thanks for hacking with us!";
const HELP: &str = "Enter ':h' for help, or ':q' to quit.";

pub struct Repl {
    interpreter: Interpreter,
    backend: Box<dyn Backend>,
    flags: sys::Flags,
}

impl Repl {
    pub fn new(backend: Box<dyn Backend>, flags: sys::Flags) -> Repl {
        Repl {
            interpreter: Interpreter::new(),
            backend,
            flags,
        }
    }

    pub fn run(&mut self) {
        self.greet();
        loop {
            let input = self.get_input();
            match input.as_str() {
                ":c" => {
                    self.show_circuit();
                }
                ":h" => {
                    self.help();
                }
                ":q" => {
                    break;
                }
                ":w" => {
                    self.wheek();
                }
                s => {
                    if let Err(errors) = self.handle_input(s) {
                        self.handle_errors(errors);
                    }
                }
            }
        }
        self.farewell();
    }

    fn handle_input(&self, input: &str) -> Result<(), Vec<Box<dyn errors::Error>>> {
        let source = SourceObject::from_src(input);
        let scanner = Scanner::new(source);
        let tokens = scanner.tokenize()?;
        let ast = Parser::new(tokens).expression();
        println!("{:?}", ast);
        Ok(())
    }

    fn handle_errors(&self, errors: Vec<Box<dyn errors::Error>>) {
        for err in errors {
            eprintln!("{}", err);
        }
    }

    fn greet(&self) {
        println!("{}", WELCOME);
        if self.flags.debug {
            println!("This interpreter is running in DEBUG mode.");
        }
        println!("{}", HELP);
    }

    fn farewell(&self) {
        println!("{}", GOODBYE);
    }

    fn help(&self) {
        println!(
            "{}\nFeel free to email {} with questions.",
            HELP,
            sys::CONTACT_ADDRESS
        );
    }

    fn show_circuit(&self) {
        eprintln!("This feature is not yet implemented.");
    }

    // An undocumented behavior of the repl
    fn wheek(&self) {
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
