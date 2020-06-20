/// This build script is used to generate a version string for error logging. It
/// is copied (almost) verbatim from Christian Vallentin's helpful example at
/// https://vallentin.dev/2019/06/06/versioning.
use std::env::{
    self,
    consts::{ARCH, OS},
};
use std::fs;
use std::path::Path;
use std::process::Command;

#[cfg(debug_assertions)]
const BUILD_TYPE: &'static str = "debug";
#[cfg(not(debug_assertions))]
const BUILD_TYPE: &'static str = "release";

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let version_path = Path::new(&out_dir).join("version");

    let version_string = format!(
        "{} {} ({}:{}{}, {} build, {} [{}])",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        get_branch_name(),
        get_commit_hash(),
        if is_working_tree_clean() { "" } else { "+" },
        BUILD_TYPE,
        OS,
        ARCH
    );

    fs::write(version_path, version_string).unwrap();
}

fn get_commit_hash() -> String {
    let output = Command::new("git")
        .arg("log")
        .arg("-1")
        .arg("--pretty=format:%h")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap();

    assert!(output.status.success());

    String::from_utf8_lossy(&output.stdout).to_string()
}

fn get_branch_name() -> String {
    let output = Command::new("git")
        .arg("rev-parse")
        .arg("--abbrev-ref")
        .arg("HEAD")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap();

    assert!(output.status.success());

    let mut branch = String::from_utf8_lossy(&output.stdout).to_string();
    if branch.ends_with('\n') {
        branch.pop();
        if branch.ends_with('\r') {
            branch.pop();
        }
    }
    branch
}

fn is_working_tree_clean() -> bool {
    let status = Command::new("git")
        .arg("diff")
        .arg("--quiet")
        .arg("--exit-code")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .status()
        .unwrap();

    status.code().unwrap() == 0
}
