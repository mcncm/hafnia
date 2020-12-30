use crate::sys;
use std::error::Error;
use std::fmt;

/// The main trait for language errors encountered in lexing, parsing, semantic
/// analysis, and code generation.
pub trait Diagnostic: Error {
    fn level(&self) -> &DiagnosticLevel {
        &DiagnosticLevel::Error
    }
}

/// The kinds of diagnostics that can be emitted by the compiler.
pub enum DiagnosticLevel {
    /// Considered an error; will cause compilation to fail.
    Error,
    /// Considered a warning or lint; will not end compilation.
    Warn,
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    struct ExampleError {
        #[msg = "thing failed: {data}"]
        span: Span,
        data: u8,
    }

    #[test]
    fn test_example_error() {
        let err = ExampleError {
            span: Span::default(),
            data: 3,
        };
        let some_string = format!("{}", err);
        assert_eq!(some_string, "thing failed: 3");
    }
}
