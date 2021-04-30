//! Data maintained for a whole compilation session: compiler flags, error
//! handlers, and so on.

use crate::{
    arch::Arch,
    cavy_errors::{Diagnostic, ErrorBuf},
    source::SrcStore,
    target::Target,
};

pub use crate::opt::OptFlags;

use std::path::PathBuf;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Phase {
    Tokenize,
    Parse,
    /// After typechecking and lowering to MIR
    Typecheck,
    /// After running static analysis checks
    Analysis,
    /// After applying MIR optimizations
    Optimization,
    /// Translation from the MIR to the low-level IR
    Translation,
    /// The final code generation step
    CodeGen,
}

impl Default for Phase {
    fn default() -> Self {
        Phase::CodeGen
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

#[derive(Debug, PartialEq, Eq)]
pub struct OptConfig {
    /// Integer optimization level.
    pub level: u8,
    pub flags: OptFlags,
}

impl Default for OptConfig {
    fn default() -> Self {
        Self {
            level: 3,
            flags: OptFlags::default(),
        }
    }
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
    /// Optimization settings.
    pub opt: OptConfig,
    /// Which compilation phases to run
    pub phase_config: PhaseConfig,
}
