use crate::{
    context::Context,
    source::Span,
    sys,
    util::{FmtWith, FmtWrapper},
};
use std::{error::Error, fmt};

/// The main trait for language errors encountered in lexing, parsing, semantic
/// analysis, and code generation.
pub trait Diagnostic: std::fmt::Debug {
    fn level(&self) -> &DiagnosticLevel {
        &DiagnosticLevel::Error
    }

    /// Formats the leading line of the error, warning, or lint message.
    fn message(&self, ctx: &Context, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    /// Retrieves messages referencing spans of source code, of which there must
    /// be at least one.
    fn spans(&self) -> Vec<SpanReport> {
        Vec::new()
    }

    /// Returns the error code
    fn error_code(&self) -> &str;
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

/// A message about a region of code. This can be used to present the results of
pub struct SpanReport<'a> {
    pub span: Span,
    pub msg: Option<Box<dyn Fn(&mut fmt::Formatter<'_>, &Context) -> fmt::Result + 'a>>,
}

impl<'c, 'a> FmtWith<Context<'c>> for SpanReport<'a> {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let src = &ctx.srcs[self.span.src_id];
        let line = src.get_line(self.span.start);
        if src.get_line(self.span.end).code != line.code {
            // FIXME assume for now that spans don't cross lines
            return f.write_str("Multiline span");
        }
        // Columns to annotate: remember that columns are 1-indexed.
        let start = self.span.start - line.start;
        let end = self.span.end - line.start;
        // How many tabs in the run-up to the start?
        let tabs = line
            .chars()
            .take(start.saturating_sub(1))
            .filter(|&c| c == '\t')
            .count();
        // Carets
        let annot = "^".repeat(end - start + 1);
        // How long should line numbers be?
        let digits = util::count_digits(line.linum.into());
        // Reported code with annotations. This is a little ad-hoc, and should
        // really be some kind of "join" over reported lines.
        write!(
            f,
            "\
{s:digits$} |
{linum:digits$} | {}
{s:digits$} | {s:\t<tabs$}{s:start$}{} ",
            line,
            annot,
            linum = line.linum,
            s = "",
            tabs = tabs,
            digits = digits,
            // start of annotation
            start = start - tabs
        )?;

        if let Some(msg) = &self.msg {
            msg(f, ctx)?;
        }

        Ok(())
    }
}

/// It's sometimes convenient to have a placeholder Error type to propagate
/// errors upward. In fact, we'll use this to approximate exceptions in several
/// compiler passes. I'm not sure if that's "good Rust," but it seems to make
/// for a nice design in which I only need to check *once* whether there have
/// been any errors in a compiler pass.
#[derive(Debug, PartialEq, Eq)]
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

impl<'c> FmtWith<Context<'c>> for ErrorBuf {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.iter().fold(true, |first, err| {
            if !first {
                // NOTE This is correct: can't return an `Err` from this
                // closure.
                let _ = f.write_str("\n");
            }
            let _ = write!(f, "{}", err.fmt_with(ctx));
            false
        });
        Ok(())
    }
}

impl<'c> FmtWith<Context<'c>> for Box<dyn Diagnostic> {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // FIXME clean up
        write!(f, "{} ", self.error_code())?;
        self.message(ctx, f)?;
        writeln!(f)?;

        for span_report in self.spans() {
            let span = span_report.span;
            let origin = &ctx.srcs[span.src_id];
            let startln = origin.get_line(span.start);
            let endln = origin.get_line(span.end);
            write!(f, "{} ", origin)?;
            if startln.linum == endln.linum {
                if span.start == span.end {
                    write!(f, "[{}:{}]", startln.linum, span.start - startln.start)?;
                } else {
                    write!(
                        f,
                        "[{}:{}-{}]",
                        startln.linum,
                        span.start - startln.start,
                        span.end - startln.start
                    )?;
                }
            } else {
                write!(
                    f,
                    "[{}:{}]-[{}:{}]",
                    startln.linum,
                    span.start - startln.start,
                    endln.linum,
                    span.end - endln.end
                )?;
            }
            writeln!(f, "\n{}", span_report.fmt_with(ctx))?;
        }
        Ok(())
    }
}

/// Internal helper functions
mod util {
    /// Count the decimal digits in a number; useful for formatting lines of
    /// source code.
    pub const fn count_digits(n: usize) -> usize {
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
    #[msg = "thing failed: {data}"]
    struct ExampleError {
        #[span]
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
