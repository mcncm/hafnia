//! Data maintained for a whole compilation session: compiler flags, error
//! handlers, and so on.

use crate::arch::Arch;
use crate::cavy_errors::{Diagnostic, ErrorBuf};
use crate::source::SrcStore;
use crate::target::Target;
use std::path::PathBuf;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Phase {
    Tokenize,
    Parse,
    /// Shorthand for all semantic-analysis passes
    Typecheck,
    /// The tree-walk interpreter: this will be replaced with a `codegen` phase
    /// or something to that effect.
    Evaluate,
}

impl Default for Phase {
    fn default() -> Self {
        Phase::Evaluate
    }
}

/// Encodes which passes to do, including when to stop and which passes to skip.
#[derive(Debug, PartialEq, Eq, Default)]
pub struct PhaseConfig {
    /// Included because we might want to go on to evaluation, but skip
    /// semantic analysis.
    pub typecheck: bool,
    /// Specifies what phase of the pipeline to stop at
    pub last_phase: Phase,
}

/// Configuration data for the operation of the compiler
#[derive(Debug, Default)]
pub struct Config {
    /// Whether or not to run in debug mode. In this mode, the default panic
    /// handler will be used.
    pub debug: bool,
    /// Architecture data
    pub arch: Arch,
    /// Compile target data
    pub target: Box<dyn Target>,
    /// Optimization level.
    pub opt: u8,
    /// Which compilation phases to run
    pub phase_config: PhaseConfig,
}

/// The main Session type containing all data that should be accessible to
/// many compiler passes.
#[derive(Debug, Default)]
pub struct Session {
    /// Configuration data used throughout compilation
    pub config: Config,
    /// The source files used during compilation
    pub sources: SrcStore,
}

impl Session {
    pub fn new(config: Config) -> Self {
        Self {
            config,
            sources: SrcStore::new(),
        }
    }

    pub fn emit_diagnostics(&self, errors: ErrorBuf) {
        for err in errors.0.into_iter() {
            let msg = self.sources.format_err(err);
            eprintln!("{}", msg);
        }
    }
}
