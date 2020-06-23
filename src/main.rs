use std::fs;
use std::io;
use std::panic;
use std::path::Path;
use std::process;

use cavy::backend;
use cavy::repl::Repl;
use cavy::sys;

use clap::{load_yaml, App, ArgMatches};

fn get_backend(_argmatches: &ArgMatches) -> Box<dyn backend::Backend> {
    Box::new(backend::NullBackend::new())
}

fn get_flags(argmatches: &ArgMatches) -> sys::Flags {
    let debug = argmatches.is_present("debug");
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

    sys::Flags { debug, opt }
}

fn get_code(argmatches: &ArgMatches) -> Result<Option<String>, io::Error> {
    match argmatches.value_of("INPUT") {
        Some(path) => {
            let source_path = Path::new(&path);
            Ok(Some(fs::read_to_string(&source_path)?))
        }
        None => Ok(None),
    }
}

fn main() {
    #[cfg(not(debug_assertions))] // release build only
    {
        use cavy::errors;
        eprintln!("Warning: crash reporting is not fully implemented.");
        panic::set_hook(Box::new(errors::panic_hook));
    }

    let yaml = load_yaml!("cli.yml");
    let argmatches = App::from(yaml).get_matches();
    let backend = get_backend(&argmatches);
    let flags = get_flags(&argmatches);
    match get_code(&argmatches) {
        // A source file was given and read without error
        Ok(Some(_code)) => {
            todo!();
        }
        // A source file was not given; run a repl
        Ok(None) => {
            let mut repl = Repl::new(backend, flags);
            repl.run();
        }
        // An error was encountered in reading a source file
        Err(_) => {
            eprintln!("Failed to read source file.");
            process::exit(1);
        }
    }
}
