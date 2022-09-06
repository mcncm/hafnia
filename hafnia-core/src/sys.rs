//! Utilities for setting up the compiler process, finding files, and
//! information about the Hafnia system.

use std::panic::PanicInfo;
use std::path::{Path, PathBuf};

pub const VERSION_STRING: &str = include_str!(concat!(env!("OUT_DIR"), "/version"));

/// Exit (relatively) gracefully, informing the user if there has been an error,
/// although they'll likely know this anyway from diagnostic messages.
pub fn exit(code: i32) -> ! {
    if code != 0 {
        eprintln!("Hafnia exited with errors.")
    }
    std::process::exit(code);
}

pub fn panic_hook(info: &PanicInfo) {
    eprintln!(
        "Hafnia has encountered an unexpected error. This is a bug.
Please report it to the developers."
    );

    eprintln!("build:\t{}", VERSION_STRING);
    if let Some(info) = info.payload().downcast_ref::<&str>() {
        eprintln!("info:\t{}", info);
    }
    if let Some(loc) = info.location() {
        eprintln!("loc:\t{}", loc);
    }
}
