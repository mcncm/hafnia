use crate::source::Span;
use crate::sys;
use std::error::Error;
use std::fmt;

/// The main trait for language errors encountered in lexing, parsing, semantic
/// analysis, and code generation.
pub trait Diagnostic: std::fmt::Debug {
    fn level(&self) -> &DiagnosticLevel {
        &DiagnosticLevel::Error
    }

    /// Formats the leading line of the error, warning, or lint message.
    fn message(&self) -> String;

    /// Retrieves the main Span corresponding to the error
    fn main_span(&self) -> &Span;

    /// Returns the error code
    fn code(&self) -> &str;
}

/// Like `std::error::Error`, we would often like to enjoy automatic conversion
/// to a boxed error type.
impl<'a, T: Diagnostic + 'a> From<T> for Box<dyn Diagnostic + 'a> {
    fn from(value: T) -> Self {
        Box::new(value)
    }
}

/// The kinds of diagnostics that can be emitted by the compiler.
pub enum DiagnosticLevel {
    /// Considered an error; will cause compilation to fail.
    Error,
    /// Considered a warning or lint; will not end compilation.
    Warn,
}

/// It's sometimes convenient to have a placeholder Error type to propagate
/// errors upward. In fact, we'll use this to approximate exceptions in several
/// compiler passes. I'm not sure if that's "good Rust," but it seems to make
/// for a nice design in which I only need to check *once* whether there have
/// been any errors in a compiler pass.
#[derive(Debug)]
pub struct CavyError;

impl std::fmt::Display for CavyError {
    /// Should never actually be called
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!()
    }
}

impl Error for CavyError {}

/// Let’s simplify error propagation with with a typedef. This should be an
/// acceptable thing to do; it mimics `io::Result`, and it's seen in plenty of
/// projects.
pub type Result<T> = std::result::Result<T, CavyError>;

#[derive(Debug)]
pub struct ErrorBuf(pub Vec<Box<dyn Diagnostic>>);

impl ErrorBuf {
    pub fn new() -> Self {
        Self(vec![])
    }

    /// It's useful for this to return something implementing Error; we'll use
    /// this placeholder type to achieve this.
    pub fn push<T: 'static + Diagnostic>(&mut self, err: T) -> CavyError {
        self.0.push(Box::new(err));
        CavyError
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
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
        let _err = ExampleError {
            span: Span::default(),
            data: 3,
        };
    }
}
