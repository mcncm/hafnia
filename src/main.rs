use std::fs;
use std::io::{self, prelude::*};
use std::panic;
use std::path::{Path, PathBuf};
use std::process;

use cavy::repl::Repl;
use cavy::{compile, sys};

use clap::{load_yaml, App, ArgMatches};
use fs::File;

fn get_flags(argmatches: &ArgMatches) -> sys::Flags {
    // Should we provide debug information?
    let debug = argmatches.is_present("debug");

    // Where should we cut the pipeline short?
    let mut phase = sys::CompilerPhase::Evaluate;
    if argmatches.is_present("typecheck") {
        phase = sys::CompilerPhase::Typecheck;
    } else if argmatches.is_present("parse") {
        phase = sys::CompilerPhase::Parse;
    } else if argmatches.is_present("tokenize") {
        phase = sys::CompilerPhase::Tokenize;
    }

    // Should this fail silently?
    let opt = match argmatches.value_of("opt") {
        Some("1") => 1,
        Some("2") => 2,
        Some("3") => 3,
        _ => 0,
    };
    if opt > 0 {
        println!(
            "Running with optimization level {}. This option currently does nothing.",
            opt
        );
    }

    sys::Flags { debug, opt, phase }
}

fn get_code(argmatches: &ArgMatches) -> Result<Option<(String, String)>, io::Error> {
    match argmatches.value_of("INPUT") {
        Some(path) => {
            let source_path = PathBuf::from(&path);
            Ok(Some((path.to_string(), fs::read_to_string(&source_path)?)))
        }
        None => Ok(None),
    }
}

fn main() {
    let yaml = load_yaml!("cli.yml");
    let argmatches = App::from(yaml).get_matches();
    let flags = get_flags(&argmatches);

    // Only emit debug messages if the program has *not* been built for the
    // `release` profile, *and* the --debug flag has been passed.
    #[cfg(not(debug_assertions))]
    {
        use cavy::errors;
        panic::set_hook(Box::new(errors::panic_hook));
    }

    #[cfg(debug_assertions)]
    {
        use cavy::errors;
        if !flags.debug {
            panic::set_hook(Box::new(errors::panic_hook));
        }
    }

    match get_code(&argmatches) {
        // A source file was given and read without error
        Ok(Some(src)) => {
            let object_path = Path::new(argmatches.value_of("OBJECT").unwrap_or("a.qasm"));
            let object_code = compile::compile(src, flags).unwrap();
            let mut file = File::create(&object_path).unwrap();
            file.write_all(object_code.as_bytes()).unwrap();
            process::exit(0);
        }
        // A source file was not given; run a repl
        Ok(None) => {
            let mut repl = Repl::new(flags);
            repl.run();
        }
        // An error was encountered in reading a source file
        Err(_) => {
            eprintln!("Failed to read source file.");
            process::exit(1);
        }
    }
}
