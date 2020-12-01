use crate::backend::Backend;
use crate::errors::{self, ErrorBuf};
use crate::interpreter::Interpreter;
use crate::parser::Parser;
use crate::scanner::{Scanner, SourceCode};
use crate::{ast::Stmt, sys};
use std::fmt::Display;
use std::io::{self, Write};

const UNICODE_PROMPT: &str = "ψ⟩ ";
const ASCII_PROMPT: &str = "> ";
const WELCOME: &str = "Welcome to the alpha version of the Cavy repl!";
const GOODBYE: &str = "Thanks for hacking with us!";
const HELP: &str = "Enter ':h' for help, or ':q' to quit.";

pub struct Repl {
    interpreter: Interpreter,
    flags: sys::Flags,
}

impl Repl {
    pub fn new(flags: sys::Flags) -> Repl {
        Repl {
            interpreter: Interpreter::new(),
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
                ":f" => {
                    println!("{:?}", self.flags);
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

    fn handle_input(&mut self, input: &str) -> Result<(), ErrorBuf> {
        let source = SourceCode::from_src(input);

        let tokens = Scanner::new(source).tokenize()?;
        if self.flags.phase <= sys::CompilerPhase::Tokenize {
            // I wonder if there’s another way to factor this code so that I
            // don’t have to make these tests every time I handle input... Not
            // that it’s actually a performance bottleneck.
            println!("{:?}", tokens);
            return Ok(());
        }

        let stmts = Parser::new(tokens).parse()?;

        if self.flags.phase <= sys::CompilerPhase::Parse {
            println!("{:?}", stmts);
            return Ok(());
        }

        if self.flags.phase <= sys::CompilerPhase::Typecheck {
            todo!();
        }

        let len = stmts.len();
        for (n, stmt) in stmts.iter().enumerate() {
            match stmt {
                Stmt::Expr(expr) => {
                    let value = self.interpreter.evaluate(&expr)?;
                    // Print the value of the final *expression* only
                    if n == len - 1 {
                        println!("{:?}", value);
                    };
                }
                stmt => {
                    self.interpreter.execute(&stmt)?;
                }
            }
        }
        Ok(())
    }

    fn handle_errors(&self, errors: ErrorBuf) {
        eprintln!("{}", errors);
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
        println!("{}", self.interpreter.circuit);
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
