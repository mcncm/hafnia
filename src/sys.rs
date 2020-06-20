use std::path::{Path, PathBuf};

pub const VERSION_STRING: &str = include_str!(concat!(env!("OUT_DIR"), "/version"));

pub fn cavy_dir() -> Option<PathBuf> {
    dirs::home_dir().map(|dir| dir.join(Path::new(".cavy")))
}

pub fn crashlog_path() -> Option<PathBuf> {
    cavy_dir().map(|dir| dir.join(Path::new("crashlog.json")))
}

pub struct Flags {
    pub debug: bool,
    pub opt: u8,
}
