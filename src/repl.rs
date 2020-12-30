use crate::arch::Arch;
use crate::cavy_errors::{self, ErrorBuf};
use crate::interpreter::Interpreter;
use crate::parser::Parser;
use crate::scanner::Scanner;
use crate::source::{SrcObject, SrcStore};
use crate::typecheck;
use crate::{ast::StmtKind, sys};
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::fmt::Display;
use std::io::{self, Write};
use std::process;

const UNICODE_PROMPT: &str = "ψ⟩ ";
const ASCII_PROMPT: &str = "> ";
const WELCOME: &str = "Welcome to the alpha version of the Cavy repl!";
const GOODBYE: &str = "Thanks for hacking with us!";
const HELP: &str = "Enter ':h' for help, or ':q' to quit.";

/// NOTE this struct is very similar to `functions::builtins::Builtin`. Should
/// they be unified?
struct CmdSpec<'a> {
    // FIXME Ok, this lifetime problem is getting a little bit ugly. I'll just
    // use owned strings here. It's not ideal, but at least it isn't in
    // some tight innner loop.
    func: &'a dyn Fn(&Repl<'a>, Vec<String>),
    arity: usize,
    desc: &'a str,
}

// NOTE this macro is very similar to functions::builtins::builtins_table.
macro_rules! command_table {
    ($lt:lifetime, $($cmd:expr => $func:ident : $arity:expr ; $desc:expr),*) => {
        {
            type Cmd<$lt> = &$lt dyn Fn(&Repl<$lt>, Vec<String>);
            let mut table = HashMap::new();
            $(
                table.insert(
                    $cmd,
                    CmdSpec {
                        func: &Repl::$func as Cmd<$lt>,
                        arity: $arity,
                        desc: $desc,
                    },
                );
            )*
            table
        }
    };
}

pub struct Repl<'a> {
    src_store: SrcStore,
    interpreter: Interpreter<'a>,
    flags: &'a sys::Flags,
    commands: HashMap<&'a str, CmdSpec<'a>>,
}

impl<'a> Repl<'a> {
    pub fn new(flags: &'a sys::Flags, arch: &'a Arch) -> Self {
        // Set up commands. We can’t do this in a lazy_static because some
        // impossible trait bounds would be required, but that’s ok--we’re
        // setting up this table exactly once on startup, anyway!
        let commands = command_table! [
            'a,
            ":h" => help : 0 ; "Help (you are here!)",
            ":q" => quit : 0 ; "Quit the repl environment",
            ":c" => show_circuit : 0 ; "Display the circuit built so far"
        ];

        Repl {
            src_store: SrcStore::default(),
            interpreter: Interpreter::new(&arch),
            flags,
            commands,
        }
    }

    pub fn run(&'a mut self) {
        self.greet();
        loop {
            let input = self.get_input();
            let args: Vec<&str> = input.split_ascii_whitespace().collect();
            if args.is_empty() {
                continue;
            }

            // Handle a special command, if we get one.
            if let Some(CmdSpec { func, arity, .. }) = self.commands.get(args[0]) {
                if args.len() < arity + 1 {
                    eprintln!(
                        "Command '{}' expected at least {} argument.",
                        args[0], arity
                    );
                    continue;
                }
                func(self, args[1..].iter().map(|s| s.to_string()).collect());
                continue;
            }

            // Otherwise, execute code.
            if let Err(errors) = self.exec_input(input.as_str()) {
                self.handle_errors(errors);
            }
        }
    }

    fn exec_input(&mut self, input: &str) -> Result<(), ErrorBuf> {
        let phase = &self.flags.phase_config.last_phase;

        if phase < &sys::CompilerPhase::Tokenize {
            return Ok(());
        }
        let mut source = self.src_store.insert_input(input);
        let tokens = Scanner::new(&mut source).tokenize()?;

        if phase < &sys::CompilerPhase::Parse {
            // I wonder if there’s another way to factor this code so that I
            // don’t have to make these tests every time I handle input... Not
            // that it’s actually a performance bottleneck.
            println!("{:?}", tokens);
            return Ok(());
        }
        let mut stmts = Parser::new(tokens).parse()?;

        if phase < &sys::CompilerPhase::Typecheck {
            println!("{:#?}", stmts);
            return Ok(());
        }
        if self.flags.phase_config.typecheck {
            typecheck::typecheck(&mut stmts)?;
        }

        if phase < &sys::CompilerPhase::Evaluate {
            return Ok(());
        }
        let len = stmts.len();
        for (n, stmt) in stmts.iter().enumerate() {
            if let StmtKind::Expr(expr) = &stmt.kind {
                let value = self.interpreter.evaluate(&expr)?;
                // Print the value of the final *expression* only
                if n == len - 1 {
                    println!("{}", value);
                };
            } else {
                self.interpreter.execute(&stmt)?;
            }
        }
        Ok(())
    }

    fn handle_errors(&self, errors: ErrorBuf) {
        for err in errors.0.iter() {
            println!("{}", self.src_store.format_err(err.as_ref()));
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

    fn get_input(&self) -> String {
        print!("{}", UNICODE_PROMPT);
        io::stdout().flush().expect("Failed to flush stdout.");

        let mut input = String::new();
        io::stdin()
            .read_line(&mut input)
            .expect("Failed to read input.");

        input.trim().to_owned()
    }

    fn help(&self, _args: Vec<String>) {
        println!("\nContact:\n{:08}{}", "", sys::CONTACT_ADDRESS);

        println!("Repl commands:");

        for (cmd, CmdSpec { desc, .. }) in &self.commands {
            println!("{:08}{}", cmd, desc);
        }
        println!();
    }

    fn quit(&self, _args: Vec<String>) {
        self.farewell();
        process::exit(0);
    }

    fn doc(&self, _args: Vec<String>) {
        unimplemented!();
    }

    fn show_circuit(&self, _args: Vec<String>) {
        println!("{}", self.interpreter.circuit);
    }
}
