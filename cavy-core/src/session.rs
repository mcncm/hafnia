//! Data maintained for a whole compilation session: compiler flags, error
//! handlers (not currently included here), and so on.

use crate::{
    arch::Arch,
    cavy_errors::{Diagnostic, ErrorBuf},
    source::SrcStore,
    target::Target,
};

pub use crate::opt::OptFlags;

use std::path::PathBuf;

/// Compilation phases
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Phase {
    /// After scanning the program text
    Tokenize,
    /// After parsing to the AST
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
#[derive(Debug)]
pub struct Config {
    /// Whether or not to run in debug mode. In this mode, the default panic
    /// handler will be used.
    pub debug: bool,
    /// Whether to use alternative, more-canonical gate representations when
    /// possible.
    pub rerep: bool,
    /// Architecture data
    pub arch: Arch,
    /// Optimization settings.
    pub opt: OptConfig,
    /// Which compilation phases to run
    pub phase_config: PhaseConfig,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            debug: false,
            rerep: true,
            arch: Arch::default(),
            opt: OptConfig::default(),
            phase_config: PhaseConfig::default(),
        }
    }
}

// == Compiler statistics
use std::time::Instant;

#[derive(Debug)]
pub struct Event {
    pub label: &'static str,
    instant: Instant,
}

impl Event {
    /// Time difference in micros
    pub fn delta(&self, other: &Event) -> u128 {
        (self.instant - other.instant).as_micros()
    }
}

impl From<&'static str> for Event {
    fn from(label: &'static str) -> Self {
        Self {
            label,
            instant: Instant::now(),
        }
    }
}

/// Compiler statistics for performance analysis and optimization
#[derive(Debug)]
pub struct Statistics {
    pub events: Vec<Event>,
}

impl Statistics {
    pub fn new() -> Self {
        Self {
            events: vec![Event::from("init")],
        }
    }

    pub fn tick(&mut self, label: &'static str) {
        self.events.push(Event::from(label));
    }
}
