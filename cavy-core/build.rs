//! This build script is used to generate a version string for error logging. It
//! is copied (almost) verbatim from Christian Vallentin's helpful example at
//! https://vallentin.dev/2019/06/06/versioning.

use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

#[cfg(debug_assertions)]
const BUILD_TYPE: &str = "debug";
#[cfg(not(debug_assertions))]
const BUILD_TYPE: &str = "release";

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let version_path = Path::new(&out_dir).join("version");

    let version_string = format!(
        "{} ({}, {})",
        env!("CARGO_PKG_VERSION"),
        BUILD_TYPE,
        std::env::var("TARGET").unwrap(),
    );

    fs::write(version_path, version_string).unwrap();
}
