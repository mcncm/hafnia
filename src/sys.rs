use crate::target::Target;
use std::cmp::{Ord, PartialOrd};
use std::path::{Path, PathBuf};

pub const VERSION_STRING: &str = include_str!(concat!(env!("OUT_DIR"), "/version"));
pub const CONTACT_ADDRESS: &str = include_str!(concat!(env!("OUT_DIR"), "/address"));

pub fn cavy_dir() -> Option<PathBuf> {
    dirs::home_dir().map(|dir| dir.join(Path::new(".cavy")))
}

pub fn fault_log_path() -> Option<PathBuf> {
    cavy_dir().map(|dir| dir.join(Path::new("fault_log.json")))
}

pub fn history_path() -> Option<PathBuf> {
    cavy_dir().map(|dir| dir.join(Path::new(".history")))
}

/// Specifies what phase of the pipeline to stop at
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CompilerPhase {
    Tokenize,
    Parse,
    Typecheck,
    Evaluate,
}

/// Configuration data for the operation of the compiler
#[derive(Debug)]
pub struct Flags {
    pub debug: bool,
    pub opt: u8,
    pub phase: CompilerPhase,
}
