//! Utilities for setting up the compiler process, finding files, and
//! information about the Cavy system.

use std::panic::PanicInfo;
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

/// Exit (relatively) gracefully, informing the user if there has been an error,
/// although they'll likely know this anyway from diagnostic messages.
pub fn exit(code: i32) -> ! {
    if code != 0 {
        eprintln!("Cavy exited with errors.")
    }
    std::process::exit(code);
}

/// This is custom panic handler that logs system state on an unexpected crash.
pub fn panic_hook(info: &PanicInfo) {
    let fault = fault::FaultInfo::from_panic(&info);
    match fault.log() {
        // fault successfully logged
        Ok(fault_log) => {
            eprintln!(
                "Cavy has encountered an unexpected error. \
                 Please contact the developers at {}, and if possible \
                 send them the error log found at '{}'.",
                CONTACT_ADDRESS,
                fault_log.as_os_str().to_string_lossy()
            );
        }
        // fault could not be logged, for one reason or another.
        Err(err) => {
            eprintln!(
                "Cavy has encountered an unexpected error. \
                 Please contact the developers at {}.\n\
                 Fault reporting failure: {:?}",
                CONTACT_ADDRESS, err,
            );
        }
    }
}

pub mod fault {
    use crate::sys;
    use std::fs;
    use std::io::{self, Error, ErrorKind};
    use std::panic::PanicInfo;
    use std::path::PathBuf;

    use serde::{Deserialize, Serialize};
    use serde_json::{self, Value};

    // TODO: add history field without which this dump won't be very useful.
    #[derive(Serialize, Deserialize, Debug)]
    pub struct FaultInfo {
        info: String,
        version: &'static str,
    }

    impl FaultInfo {
        pub fn from_panic(panic_info: &PanicInfo) -> Self {
            FaultInfo {
                info: format!("{}", panic_info),
                version: sys::VERSION_STRING,
            }
        }

        /// Log a fault, and if successful, return the path to the fault log,
        /// for example to display it for the user.
        pub fn log(self) -> io::Result<PathBuf> {
            if let Some(fault_log) = sys::fault_log_path() {
                let mut faults = get_faults(&fault_log)?;
                faults.push(serde_json::to_value(self).unwrap());
                write_faults(&fault_log, faults)?;
                Ok(fault_log)
            } else {
                Err(Error::new(
                    ErrorKind::Other,
                    "Fault log path does not exist.",
                ))
            }
        }
    }

    fn get_faults(fault_log: &PathBuf) -> io::Result<Vec<serde_json::Value>> {
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true) // must be included with `create`
            .read(true)
            .open(&fault_log)?;

        match serde_json::from_reader(file) {
            Ok(Value::Array(values)) => Ok(values),
            Ok(_) => Err(Error::new(ErrorKind::Other, "Corrupted fault log")),
            Err(_) => Ok(vec![]), // fault log empty or corrupted; start over
        }
    }

    fn write_faults(fault_log: &PathBuf, faults: Vec<Value>) -> io::Result<()> {
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(&fault_log)?;

        serde_json::to_writer(file, &Value::Array(faults)).map_err(|e| e.into())
    }
}
