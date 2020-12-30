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

/// Let’s simplify error propagation with with a typedef. This should be an
/// acceptable thing to do; it mimics `io::Result`, and it's seen in plenty of
/// projects.
pub type Result<T> = std::result::Result<T, Box<dyn Diagnostic>>;

/// It is common to want to report multiple errors from a single compiler pass;
/// therefore it will be helpful to have such a buffer to push errors into as
/// they’re encountered, and report them all together.
///
/// The one thing that could be a little awkward about this definition is that
/// it’s actually recursive, and an `ErrorBuf` of `ErrorBuf`s might be
/// nonsensical. I could break the recursion by implementing my own Error type
/// for `ErrorBuf` instead of the standard library one.
#[derive(Debug)]
pub struct ErrorBuf(pub Vec<Box<dyn Diagnostic>>);

impl ErrorBuf {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn push(&mut self, err: Box<dyn Diagnostic>) {
        self.0.push(err)
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
