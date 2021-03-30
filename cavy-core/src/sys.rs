//! Utilities for setting up the compiler process, finding files, and
//! information about the Cavy system.

use std::panic::PanicInfo;
use std::path::{Path, PathBuf};

pub const VERSION_STRING: &str = include_str!(concat!(env!("OUT_DIR"), "/version"));
pub const CONTACT_ADDRESS: &str = include_str!(concat!(env!("OUT_DIR"), "/address"));

/// Exit (relatively) gracefully, informing the user if there has been an error,
/// although they'll likely know this anyway from diagnostic messages.
pub fn exit(code: i32) -> ! {
    if code != 0 {
        eprintln!("Cavy exited with errors.")
    }
    std::process::exit(code);
}

pub fn panic_hook(info: &PanicInfo) {
    eprintln!(
        "Cavy has encountered an unexpected error.
Please contact the developers at {} with your source code
and the following diagnostic information:\n",
        CONTACT_ADDRESS
    );

    eprintln!("build:\t{}", VERSION_STRING);
    if let Some(info) = info.payload().downcast_ref::<&str>() {
        eprintln!("info:\t{}", info);
    }
    if let Some(loc) = info.location() {
        eprintln!("loc:\t{}", loc);
    }
}
