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

pub struct Flags {
    pub debug: bool,
    pub opt: u8,
}
