use crate::source::Span;
use crate::{
    context::{Context, CtxFmt},
    sys,
};
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

impl<'t> CtxFmt<'t, DiagnosticFmt<'t>> for Box<dyn Diagnostic> {
    fn fmt_with(&'t self, ctx: &'t Context) -> DiagnosticFmt<'t> {
        DiagnosticFmt { err: self, ctx }
    }
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

/// Simplify error propagation with a typedef. This should be an acceptable
/// thing to do; it mimics `io::Result`, and it's seen in plenty of projects.
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

pub struct DiagnosticFmt<'d> {
    // Ok, it isn't really any loss to have a `Box` here, since we'll only ever
    // use this through a `Box`. But it does annoy me that I can't figure out
    // how to accomplish this with just a `&'d dyn Diagnostic`.
    err: &'d Box<dyn Diagnostic>,
    ctx: &'d Context<'d>,
}

impl<'d> fmt::Display for DiagnosticFmt<'d> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {}\n{}",
            self.err.code(),
            self.err.message(),
            self.format_span(self.err.main_span()),
        )
    }
}

impl<'d> DiagnosticFmt<'d> {
    /// Format the main span of a diagnostic. consider implementations that
    /// could avoid the extra allocation.
    fn format_span(&self, span: &Span) -> String {
        let src = &self.ctx.srcs[span.src_id];
        let line = src.get_line(span.start);
        // FIXME assume for now that spans don't cross lines
        if src.get_line(span.end) != line {
            panic!("Span crossed a line boundary");
        }
        // Columns to annotate: remember that columns are 1-indexed.
        let start = span.start.col;
        let end = span.end.col;
        // Carets
        let annot = "^".repeat(end - start + 1);
        // How long should line numbers be?
        let digits = util::count_digits(span.start.line);
        // Reported code with annotations. This is a little ad-hoc, and should
        // really be some kind of "join" over reported lines.
        let origin = format!("{} {}", src.origin, span);
        let report = format!(
            "{s:digits$} |\n{s:digits$} | {}\n{s:digits$} | {s:start$}{}",
            line,
            annot,
            s = "",
            digits = digits,
            // start of annotation
            start = start - 1
        );
        format!("{}\n{}", origin, report)
    }
}

/// Internal helper functions
mod util {
    /// Count the digits in a number; useful for formatting lines of source code.
    pub fn count_digits(n: usize) -> usize {
        match n {
            0 => 1,
            mut n => {
                let mut digits = 0;
                while n > 0 {
                    n /= 10;
                    digits += 1;
                }
                digits
            }
        }
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
