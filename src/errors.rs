use crate::sys;
use std::fmt;
use std::{error::Error, panic::PanicInfo};

/// Let’s simplify error propagation with with a typedef. This should be an
/// acceptable thing to do; it mimics `io::Result`, and it's seen in plenty of
/// projects.
pub type Result<T> = std::result::Result<T, Box<dyn Error>>;

/// It is common to want to report multiple errors from a single compiler pass;
/// therefore it will be helpful to have such a buffer to push errors into as
/// they’re encountered, and report them all together.
///
/// The one thing that could be a little awkward about this definition is that
/// it’s actually recursive, and an `ErrorBuf` of `ErrorBuf`s might be
/// nonsensical. I could break the recursion by implementing my own Error type
/// for `ErrorBuf` instead of the standard library one.
pub struct ErrorBuf(pub Vec<Box<dyn Error>>);

impl ErrorBuf {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn push(&mut self, err: Box<dyn Error>) {
        self.0.push(err)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Debug for ErrorBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for ErrorBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut repr = String::from("Errors:\n");
        for (n, err) in self.0.iter().enumerate() {
            repr.push_str(&format!("{}.\t{}\n", n, err));
        }
        write!(f, "{}", repr)
    }
}

/// These are all default implementations for the trait, for the time being.
impl Error for ErrorBuf {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }

    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }
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
                sys::CONTACT_ADDRESS,
                fault_log.as_os_str().to_string_lossy()
            );
        }
        // fault could not be logged, for one reason or another.
        Err(err) => {
            eprintln!(
                "Cavy has encountered an unexpected error. \
                 Please contact the developers at {}.\n\
                 Fault reporting failure: {:?}",
                sys::CONTACT_ADDRESS,
                err,
            );
        }
    }
}

/// This cratewide macro can be used to log an unexpected state which may or may
/// not be fatal, but does not proximally trigger a panic.
#[macro_export]
macro_rules! warn {
    () => { $crate::errors::fault::log_warning("Cavy has entered an unexpected state."); };
    ($msg:expr) => { $crate::errors::fault::log_warning($msg.to_string()); };
    ($fmt:expr, $($arg:tt),*) => {
        let info = format!($fmt, $($arg),*);
        cavy::errors::fault::log_warning(info);
    };
}

pub mod fault {
    use crate::sys;
    use std::fs;
    use std::io::{self, Error, ErrorKind};
    use std::panic::PanicInfo;
    use std::path::PathBuf;

    use serde::{Deserialize, Serialize};
    use serde_json::{self, Value};

    /// The kinds of faults that can occur and can be logged. For the time
    /// being, `Panic` is used for panics, and `Warn` by all other faults.
    #[derive(Serialize, Deserialize, Debug)]
    enum FaultLevel {
        Panic,
        Warn,
    }

    // TODO: add history field without which this dump won't be very useful.
    #[derive(Serialize, Deserialize, Debug)]
    pub struct FaultInfo {
        info: String,
        level: FaultLevel,
        version: &'static str,
    }

    impl FaultInfo {
        pub fn from_panic(panic_info: &PanicInfo) -> Self {
            FaultInfo {
                info: format!("{}", panic_info),
                level: FaultLevel::Panic,
                version: sys::VERSION_STRING,
            }
        }

        pub fn warning(info: String) -> Self {
            FaultInfo {
                info,
                level: FaultLevel::Warn,
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

    pub fn log_warning(info: String) {
        let fault = FaultInfo::warning(info.clone());
        match fault.log() {
            // fault successfully logged
            Ok(fault_log) => {
                eprintln!(
                    "Warning: {}\nThis event has been logged in '{}'.",
                    info,
                    fault_log.into_os_string().to_string_lossy()
                );
            }
            Err(_) => {
                eprintln!(
                    "Warning: {}\nThis unexpected condition could not be logged.",
                    info
                );
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
