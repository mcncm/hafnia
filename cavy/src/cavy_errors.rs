use crate::{context::CtxDisplay, source::Span};
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
    fn message(&self, ctx: &Context) -> String;

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

/// Simplify error propagation with a typedef. This should be an acceptable
/// thing to do; it mimics `io::Result`, and it's seen in plenty of projects.
/// Now, I’m not sure about the name `Maybe`. It could be confusing to Haskell
/// programmers, but on the other hand this _is_ isomorphic to `Option`:
/// `CavyError` carries no data of its own. It's also convenient to use a name
/// other than `Result` because we don't have to write `std::result::Result`
/// everywhwere we want to specify an error type.
pub type Maybe<T> = std::result::Result<T, CavyError>;

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

    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Append another ErrorBuf onto this one
    pub fn append(&mut self, other: &mut ErrorBuf) {
        self.0.append(&mut other.0)
    }
}

// ====== Display and formatting ======

impl CtxDisplay for ErrorBuf {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.iter().fold(true, |first, err| {
            if !first {
                let _ = f.write_str("\n");
            }
            let _ = write!(f, "{}", err.fmt_with(ctx));
            false
        });
        f.write_str("")
    }
}

impl CtxDisplay for Box<dyn Diagnostic> {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}\n", self.code(), self.message(ctx))?;
        format_span(self.main_span(), ctx, f)?;
        f.write_str("\n")
    }
}

/// Format the main span of a diagnostic. This could be achieved by implementing
/// `CtxDisplay` for `Span`, but there may be multiple ways we'll want to
/// display a `Span` in the future.
///
/// TODO clean up the extra, unneeded allocations in here
fn format_span(span: &Span, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let src = &ctx.srcs[span.src_id];
    let line = src.get_line(span.start);
    // FIXME assume for now that spans don't cross lines
    if src.get_line(span.end) != line {
        return f.write_str("Multiline span");
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
    write!(
        f,
        "\
{s:digits$} |
{linum:digits$} | {}
{s:digits$} | {s:start$}{}\
",
        line,
        annot,
        linum = span.start.line,
        s = "",
        digits = digits,
        // start of annotation
        start = start - 1
    )
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
