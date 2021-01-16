// use std::fs;
use std::panic;
use std::path::PathBuf;
use std::process;

use cavy::arch;
use cavy::session::{Config, Phase, PhaseConfig, Context};
// use cavy::target;
use cavy::{compile, sys};

// use cavy_cli::repl::Repl;

use clap::{load_yaml, App, ArgMatches};
// use fs::File;

/// Get the optimization level
fn get_opt(argmatches: &ArgMatches) -> u8 {
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
    opt
}

/// Collect information about which compiler phases to execute
fn get_phase(argmatches: &ArgMatches) -> PhaseConfig {
    // Where should we cut the pipeline short?
    let last_phase = match argmatches.value_of("phase") {
        Some("tokenize") => Phase::Tokenize,
        Some("parse") => Phase::Parse,
        Some("typecheck") => Phase::Typecheck,
        Some("evaluate") => Phase::Evaluate,
        Some(_) => unreachable!(),
        None => Phase::Evaluate,
    };

    // If we've gone on to a late-enough pass, should we do the typechecking
    // phase or skip it?
    let typecheck = argmatches.is_present("typecheck");

    PhaseConfig {
        last_phase,
        typecheck,
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

// fn get_target(argmatches: &ArgMatches) -> Box<dyn target::Target> {
//     match argmatches.value_of("target") {
//         Some("qasm") => Box::new(target::qasm::Qasm {}),
//         Some("latex") => Box::new(target::latex::Latex { standalone: false }),
//         Some("latex_standalone") => Box::new(target::latex::Latex { standalone: true }),
//         Some(_) => unreachable!(),
//         None => Box::new(target::qasm::Qasm {}),
//     }
// }

fn get_config(argmatches: &ArgMatches) -> Config {
    // Should we provide debug information?
    let debug = argmatches.is_present("debug");
    let opt = get_opt(argmatches);
    let phase_config = get_phase(argmatches);
    let arch = match get_arch(argmatches) {
        Ok(arch) => arch,
        Err(_) => {
            eprintln!("Failed to identify target architecture.");
            process::exit(1);
        }
    };
    // let target = get_target(argmatches);

    Config {
        debug,
        arch,
        // target,
        opt,
        phase_config,
    }
}

fn get_entry_point(argmatches: &ArgMatches) -> Option<PathBuf> {
    argmatches
        .value_of("input")
        .map(|path| PathBuf::from(&path))
}

fn get_object_path(argmatches: &ArgMatches) -> PathBuf {
    let path = argmatches.value_of("object").unwrap_or("a.out");
    PathBuf::from(path)
}

// fn emit_object_code(object_code: target::ObjectCode, object_path: PathBuf) {
//     let mut file = File::create(&object_path).unwrap();
//     file.write_all(object_code.as_bytes()).unwrap();
// }

fn main() {
    let yaml = load_yaml!("cli.yml");
    let app = App::from(yaml).version(sys::VERSION_STRING);
    let argmatches = app.get_matches();
    let config = get_config(&argmatches);
    let mut sess = Context::new(config);

    // Only emit debug messages if the program has *not* been built for the
    // `release` profile, *and* the --debug flag has been passed. The reason for
    // this is that I expect a large fraction of users to do a debug build
    // rather than a release build to test the software, and I'd like it to look
    // polished even to them.
    #[cfg(not(debug_assertions))]
    {
        panic::set_hook(Box::new(sys::panic_hook));
    }

    #[cfg(debug_assertions)]
    {
        if !sess.config.debug {
            panic::set_hook(Box::new(sys::panic_hook));
        }
    }

    match get_entry_point(&argmatches) {
        Some(path) => {
            let _object_path = get_object_path(&argmatches);
            let _object_code = compile::compile(path, &mut sess).unwrap_or_else(|errs| {
                sess.emit_diagnostics(errs);
                sys::exit(1);
            });
            // emit_object_code(object_code, object_path)
        }
        None => {
            // let mut repl = Repl::new(sess);
            // repl.run();
        }
    }
}
