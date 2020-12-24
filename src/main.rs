use std::convert::TryInto;
use std::fs;
use std::io::prelude::*;
use std::panic;
use std::path::{Path, PathBuf};
use std::process;

use cavy::arch;
use cavy::errors::ErrorBuf;
use cavy::repl::Repl;
use cavy::scanner::SourceCode;
use cavy::target;
use cavy::{compile, sys};

use clap::{load_yaml, App, ArgMatches};
use fs::File;

fn get_flags(argmatches: &ArgMatches) -> sys::Flags {
    // Should we provide debug information?
    let debug = argmatches.is_present("debug");

    // Where should we cut the pipeline short?
    let last_phase = match argmatches.value_of("phase") {
        Some("tokenize") => sys::CompilerPhase::Tokenize,
        Some("parse") => sys::CompilerPhase::Parse,
        Some("typecheck") => sys::CompilerPhase::Typecheck,
        Some("evaluate") => sys::CompilerPhase::Evaluate,
        Some(_) => unreachable!(),
        None => sys::CompilerPhase::Evaluate,
    };

    // If we've gone on to a late-enough pass, should we do the typechecking
    // phase or skip it?
    let typecheck = argmatches.is_present("typecheck");

    let phase_config = sys::CompilerPhaseConfig {
        last_phase,
        typecheck,
    };

    let opt = match argmatches.value_of("opt") {
        Some("0") => 0,
        Some("1") => 1,
        Some("2") => 2,
        Some("3") => 3,
        Some(_) => unreachable!(),
        None => 0,
    };
    if opt > 0 {
        eprintln!(
            "Warning: running with optimization level O{}. This option is currently disabled.",
            opt
        );
    }

    sys::Flags {
        debug,
        opt,
        phase_config,
    }
}

fn get_code(argmatches: &ArgMatches) -> Result<Option<SourceCode>, ErrorBuf> {
    match argmatches.value_of("input") {
        Some(path) => {
            let path = PathBuf::from(&path);
            Ok(Some(path.try_into()?))
        }
        None => Ok(None),
    }
}

fn get_arch(argmatches: &ArgMatches) -> Result<arch::Arch, Box<dyn std::error::Error>> {
    use arch::{Arch, QbCount};

    let qb_count = match argmatches.value_of("qbcount") {
        Some(qb_count) => Some(QbCount::Finite(qb_count.parse::<usize>()?)),
        None => None,
    };

    // Is there any way to make clap parse integer arguments for you?
    let qram_size = argmatches
        .value_of("qram_size")
        .unwrap_or("0")
        .parse::<usize>()
        .unwrap_or_else(|_| {
            eprintln!("Error: argument QRAM_SIZE must be a nonnegative integer.");
            process::exit(1);
        });

    let arch = match qb_count {
        Some(qb_count) => Arch {
            qb_count,
            qram_size,
        },
        None => Arch::default(),
    };

    Ok(arch)
}

fn get_target(argmatches: &ArgMatches) -> &dyn target::Target<ObjectCode = String> {
    match argmatches.value_of("target") {
        Some("qasm") => &target::qasm::Qasm {},
        Some("latex") => &target::latex::Latex { standalone: false },
        Some("latex_standalone") => &target::latex::Latex { standalone: true },
        Some(_) => unreachable!(),
        None => &target::qasm::Qasm {},
    }
}

fn main() {
    let yaml = load_yaml!("cli.yml");
    let app = App::from(yaml).version(sys::VERSION_STRING);
    let argmatches = app.get_matches();
    let flags = get_flags(&argmatches);
    let target = get_target(&argmatches);

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

    let arch = match get_arch(&argmatches) {
        Ok(arch) => arch,
        Err(_) => {
            eprintln!("Failed to identify target architecture.");
            process::exit(1);
        }
    };

    match get_code(&argmatches) {
        // A source file was given and read without error
        Ok(Some(src)) => {
            let object_path = Path::new(argmatches.value_of("object").unwrap_or("a.out"));
            let object_code = compile::compile(src, flags, &arch, target)
                .unwrap_or_else(|errs| {
                    print!("{}", errs);
                    process::exit(1);
                })
                .unwrap_or_else(|| {
                    println!("Compiler produced no object code!");
                    process::exit(0);
                });
            let mut file = File::create(&object_path).unwrap();
            file.write_all(object_code.as_bytes()).unwrap();
            process::exit(0);
        }
        // A source file was not given; run a repl
        Ok(None) => {
            let mut repl = Repl::new(&flags, &arch);
            repl.run();
        }
        // An error was encountered in reading a source file
        Err(_) => {
            eprintln!("Failed to read source file.");
            process::exit(1);
        }
    }
}
