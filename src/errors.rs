use std::fmt;

/// This trait should be implemented for all Cavy error types. It guarantees
/// that there is a way to represent the error to the user can be unwrapped.
pub trait Error: fmt::Display + fmt::Debug {}

/// This module contains this the custom panic handler that logs system state on
/// an unexpected crash.
pub mod panic {
    use crate::sys;
    use std::fs;
    use std::io::{self, Error, ErrorKind};
    use std::panic::PanicInfo;
    use std::path::PathBuf;

    use serde::{Deserialize, Serialize};
    use serde_json::{self, Value};

    // TODO: add history field without which this dump won't be very useful.
    #[derive(Serialize, Deserialize, Debug)]
    struct CrashInfo {
        panic_info: String,
        version: &'static str,
    }

    impl CrashInfo {
        fn new(panic_info: &PanicInfo) -> Self {
            CrashInfo {
                panic_info: format!("{}", panic_info),
                version: sys::VERSION_STRING,
            }
        }
    }

    pub fn panic_hook(info: &PanicInfo) {
        match log_panic(info) {
            Ok(crashlog) => {
                eprintln!(
                    "Cavy has encountered an unexpected error. \
                     Please contact the developers, and if possible \
                     send them the error log found at '{}'.",
                    crashlog.as_os_str().to_string_lossy()
                );
            }
            Err(err) => {
                //let inner_err = err.into_inner().unwrap();
                eprintln!(
                    "Cavy has encountered an unexpected error. \
                     Please contact the developers.\n\
                     Crash reporting failure: {:?}",
                    err,
                );
            }
        }
    }

    fn log_panic(info: &PanicInfo) -> io::Result<PathBuf> {
        if let Some(crashlog) = sys::crashlog_path() {
            let new_crash = CrashInfo::new(&info);
            let mut crashes = get_crashes(&crashlog)?;
            crashes.push(serde_json::to_value(new_crash).unwrap());
            write_crashes(&crashlog, crashes)?;
            Ok(crashlog)
        } else {
            Err(Error::new(
                ErrorKind::Other,
                "Crash log path does not exist.",
            ))
        }
    }

    fn get_crashes(crashlog: &PathBuf) -> io::Result<Vec<serde_json::Value>> {
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true) // must be included with `create`
            .read(true)
            .open(&crashlog)?;

        match serde_json::from_reader(file) {
            Ok(Value::Array(values)) => Ok(values),
            Ok(_) => Err(Error::new(ErrorKind::Other, "Corrupted crash log")),
            Err(_) => Ok(vec![]), // crash log empty or corrupted; start over
        }
    }

    fn write_crashes(crashlog: &PathBuf, crashes: Vec<Value>) -> io::Result<()> {
        let file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(&crashlog)?;

        serde_json::to_writer(file, &Value::Array(crashes)).map_err(|e| e.into())
    }
}
