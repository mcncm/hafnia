use std::fs;
use std::io::Write;
use std::panic;
use std::path::PathBuf;

use cavy_core::{
    arch, compile,
    context::Context,
    session::{Config, OptConfig, OptFlags, Phase, PhaseConfig, Statistics},
    sys, target,
    util::FmtWith,
};

use clap::{App, Arg, ArgMatches};
use fs::File;

/// Get the optimization level
fn get_opt(argmatches: &ArgMatches) -> OptConfig {
    let level = match argmatches.value_of("opt") {
        Some("0") => 0,
        Some("1") => 1,
        Some("2") => 2,
        Some("3") => 3,
        _ => unreachable!(),
    };
    let mut flags = OptFlags::default();
    if let Some(values) = argmatches.values_of("enable-opt") {
        for flag in values {
            flags.enable(flag);
        }
    }
    if let Some(values) = argmatches.values_of("disable-opt") {
        for flag in values {
            flags.disable(flag);
        }
    }
    OptConfig { level, flags }
}

/// Collect information about which compiler phases to execute
fn get_phase(argmatches: &ArgMatches) -> PhaseConfig {
    // Where should we cut the pipeline short?
    let last_phase = match argmatches.value_of("phase") {
        Some("tokenize") => Phase::Tokenize,
        Some("parse") => Phase::Parse,
        Some("typecheck") => Phase::Typecheck,
        Some("analysis") => Phase::Analysis,
        Some("optimization") => Phase::Optimization,
        Some("translation") => Phase::Translation,
        Some("codegen") => Phase::CodeGen,
        _ => unreachable!(),
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
        Some(qb_count) => QbCount::Finite(qb_count.parse::<usize>()?),
        None => QbCount::Infinite,
    };

    // Is there any way to make clap parse integer arguments for you?
    let qram_size = argmatches
        .value_of("qram_size")
        .unwrap_or("0")
        .parse::<usize>()
        .unwrap_or_else(|_| {
            eprintln!("Error: argument QRAM_SIZE must be a nonnegative integer.");
            sys::exit(1);
        });

    let feedback = argmatches.is_present("feedback");

    let meas_mode = match argmatches.value_of("meas_mode") {
        Some("demolition") => arch::MeasurementMode::Demolition,
        Some("nondemolition") => arch::MeasurementMode::Nondemolition,
        Some("dirty") => arch::MeasurementMode::Nondemolition,
        _ => arch::MeasurementMode::Demolition,
    };

    Ok(Arch {
        qb_count,
        qram_size,
        feedback,
        meas_mode,
        // Disable for now; no need to open this infinite can of worms
        recursion: false,
    })
}

fn get_config(argmatches: &ArgMatches) -> Config {
    // Should we provide debug information?
    let debug = argmatches.is_present("debug");
    let rerep = !argmatches.is_present("no-rerep");
    let opt = get_opt(argmatches);
    let phase_config = get_phase(argmatches);
    let arch = match get_arch(argmatches) {
        Ok(arch) => arch,
        Err(_) => {
            eprintln!("Failed to identify target architecture.");
            sys::exit(1);
        }
    };

    Config {
        debug,
        rerep,
        arch,
        opt,
        phase_config,
    }
}

fn get_target(argmatches: &ArgMatches) -> Box<dyn target::Target> {
    use target::{debug, latex, qasm, summary};

    let perf = argmatches.is_present("perf");
    let nwtarg = argmatches.is_present("nwtarg");
    let wave = argmatches.is_present("wave");
    let standalone = argmatches.is_present("standalone");
    let no_environment = argmatches.is_present("no_environment");
    let initial_kets = argmatches.is_present("initial_kets");
    let package = match argmatches.value_of("package") {
        Some("qcircuit") => latex::Package::Qcircuit { nwtarg },
        Some("quantikz") => latex::Package::Quantikz { nwtarg, wave },
        Some("yquant") => latex::Package::Yquant,
        _ => unreachable!(),
    };

    match argmatches.value_of("target") {
        Some("qasm") => Box::new(qasm::Qasm {}),
        // Need to start thinking about abstracting all this a little more
        Some("latex") => Box::new(latex::LaTeX {
            standalone,
            initial_kets,
            package,
            no_environment,
        }),
        Some("summary") => Box::new(summary::Summary { perf }),
        Some("debug") => Box::new(debug::SerialDebug {}),
        Some("null") => Box::new(target::null::NullTarget()),
        _ => unreachable!(),
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

fn emit_object_code(object_code: target::ObjectCode, object_path: PathBuf) {
    let mut file = File::create(&object_path).unwrap();
    file.write_all(object_code.as_bytes()).unwrap();
}

fn app() -> App<'static> {
    App::new("Cavyc")
        .version(sys::VERSION_STRING)
        .author("mcncm <cavy-lang-support@mit.edu")
        .about("A small, imperative quantum programming language")
        .arg(
            Arg::new("input")
                .about("The source file to compile")
                .required(false)
                .index(1),
        )
        .arg(
            Arg::new("object")
                .about("Write the compiler output into <OBJECT>.")
                .short('o')
                .value_name("OBJECT")
                .required(false),
        )
        // Target options
        .arg(
            Arg::new("target")
                .about("Object language to target.")
                .long("target")
                .short('t')
                .required(false)
                .possible_values(&["summary", "qasm", "latex", "debug", "null"])
                .default_value("qasm"),
        )
        .arg(
            Arg::new("standalone")
                .about("Compiles LaTeX output as a standalone document.")
                .long("standalone")
        )
        .arg(
            Arg::new("nwtarg")
                .about("Use nice `\nwtarg` macros in LaTeX output. Always on if `standalone`.")
                .long("nwtarg")
        )
        .arg(
            Arg::new("no_environment")
                .about(r#"Suppress `\begin{}` and `\end{}` macros in LaTeX output."#)
                .long("no-environment")
                .conflicts_with("standalone"),
        )
        .arg(
            Arg::new("wave")
                .about(r#"Separate classical and quantum bits with the quantikz `\wave`."#)
                .long("wave")
        )
        .arg(
            Arg::new("initial_kets")
                .about("Represent initial `X` gates with ket states.")
                .long("initial-kets"),
        )
        .arg(
            Arg::new("package")
                .about("<PACKAGE> is the LaTeX package used for circuit output.")
                .long("package")
                .value_name("PACKAGE")
                .required(false)
                .possible_values(&["qcircuit", "quantikz", "yquant"])
                .default_value("quantikz"),
        )
        .arg(
            Arg::new("perf")
                .about("Include profiling data in summary statistics.")
                .long("perf"),
        )
        // Compile phase options
        .arg(
            Arg::new("debug")
                .about("Runs the compiler in debug mode")
                .long("debug")
                .short('d'),
        )
        .arg(
            Arg::new("no_rerep")
                .about("Do not canonicalize gate representations")
                .long("no-rerep"),
        )
        .arg(
            Arg::new("phase")
                .about("<PHASE> is the last phase of the compiler to run.")
                .value_name("PHASE")
                .required(false)
                .long("phase")
                .possible_values(&[
                    "tokenize",
                    "parse",
                    "typecheck",
                    "analysis",
                    "optimization",
                    "translation",
                    "codegen",
                ])
                .default_value("codegen"),
        )
        .arg(
            Arg::new("typecheck")
                .about("Run the static type checking pass (override).")
                .long("typecheck"),
        )
        // Optimization options
        .arg(
            Arg::new("opt")
                .about("Set the optimization level.")
                .long("opt-level")
                .short('O')
                .possible_values(&["0", "1", "2", "3"])
                .default_value("3")
                .required(false),
        )
        .arg(
            Arg::new("enable_opt")
                .about(
                    "Enable a specific optimization, regardless of optimization level.",
                )
                .long("enable-opt")
                .short('E')
                .possible_values(&["constprop", "unipotence"])
                .multiple_values(true),
        )
        .arg(
            Arg::new("disable_opt")
                .about(
                    "Disable a specific optimization, regardless of optimization level.",
                )
                .long("disable-opt")
                .short('D')
                .possible_values(&["constprop", "unipotence"])
                .multiple_values(true),
        )
        // Architectural options
        .arg(
            Arg::new("qubit_count")
                .about("<QBCOUNT> is the number of physical qubits.")
                .long("qubit-count")
                .short('q')
                .value_name("QBCOUNT")
                .required(false),
        )
        .arg(
            Arg::new("qram_size")
                .about("<QRAM_SIZE> is the number of addressable random access qubits.")
                .long("qram-size")
                .value_name("QRAM_SIZE"),
        )
        .arg(Arg::new("feedback").about("Enables classical feedback.").long("feedback"))
        .arg(
            Arg::new("meas_mode")
                .about(
                    "<MODE> determines the state of a hardware qubit after a projective measurement.",
                )
                .value_name("MODE")
                .long("meas-mode")
                .short('m')
                .possible_values(&["demolition", "nondemolition", "dirty"])
                .default_value("demolition")
        )
}

fn main() {
    // Should be the very first thing that is called, in order to diagnose the
    // performance of every part of the process.
    let mut stats = Statistics::new();

    let argmatches = app().get_matches();

    stats.tick("argparsing");

    let conf = get_config(&argmatches);
    let mut ctx = Context::new(&conf, &mut stats);

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
        if !ctx.conf.debug {
            panic::set_hook(Box::new(sys::panic_hook));
        }
    }

    if let Some(path) = get_entry_point(&argmatches) {
        let object_path = get_object_path(&argmatches);
        let id = ctx.srcs.insert_path(path).unwrap();
        let target = get_target(&argmatches);
        let object_code = compile::compile_target(id, &mut ctx, target).unwrap_or_else(|errs| {
            eprintln!("{}", errs.fmt_with(&ctx));
            sys::exit(1);
        });
        if let Some(object_code) = object_code {
            emit_object_code(object_code, object_path);
        }
    }
}
