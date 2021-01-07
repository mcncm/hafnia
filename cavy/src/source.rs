//! Data strucures for holding and manipulating source code

use crate::cavy_errors::{Diagnostic, ErrorBuf};
use crate::store_triple;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::path::PathBuf;

/// Count the digits in a number; useful for formatting lines of source code.
fn count_digits(n: usize) -> usize {
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

// /// Unique identifier of a source object. I'll be surprised if anyone ever needs more
// /// than two bytes to identify all of their source objects.
store_triple! { SrcStore : SrcId => SrcObject }

/// Type returned by the public SrcStore interface. This is expected to be
/// passed to a Scanner.
#[derive(Debug)]
pub struct SrcObject {
    /// The locations of newline characters within the source object: filled in
    /// by the scanner
    pub newlines: Vec<usize>,
    pub code: String,
    pub origin: String,
}

impl SrcObject {
    /// Returns a slice to the line in the source containing a point. This is
    /// expected to be called only after a scanning phase has filled in the
    /// newlines, but that isn't invariant enforced (yet) by the type system.
    ///
    /// ```text
    /// ---n_1---n_2---n_3---
    ///  ^  ^  ^  ^  ^  ^  ^
    ///  |  |  |  |  |  |  |
    ///  0  |  1  |  2  |  3   insert position
    ///     0     1     2      found position
    ///
    ///  ```
    fn get_line(&self, pos: SrcPoint) -> &str {
        // Pointing to a newline character shouldn't happen; actual spans
        // shouldn't point *at* newlines, but they might cross them.
        let n = self
            .newlines
            .binary_search(&pos.pos)
            .expect_err("SrcPoint pointed at newline");
        // line start: inclusive if pointing to first line, exclusive
        // otherwise (to exclude newline character)
        let ln_start = match n {
            0 => 0,
            n => self.newlines[n - 1],
        };

        // line end
        let ln_end = if n == self.newlines.len() {
            self.code.len()
        } else {
            // don’t include the newline itself
            self.newlines[n] - 1
        };

        &self.code[ln_start..ln_end]
    }
}

impl From<&'static str> for SrcObject {
    fn from(code: &'static str) -> Self {
        Self {
            code: code.to_owned(),
            newlines: vec![],
            origin: String::from("<static>"),
        }
    }
}

impl SrcStore {
    /// Try to insert a path to a source file and retrieve a source object
    pub fn insert_path(&mut self, path: PathBuf) -> Result<SrcId, std::io::Error> {
        let code = std::fs::read_to_string(&path)?;
        let src = SrcObject {
            newlines: vec![],
            code,
            origin: path.to_string_lossy().to_string(),
        };
        Ok(self.insert(src))
    }

    pub fn insert_input(&mut self, input: &str) -> SrcId {
        let src = SrcObject {
            newlines: vec![],
            code: input.to_owned(),
            origin: "<input>".to_owned(),
        };
        self.insert(src)
    }

    pub fn format_err(&self, err: Box<dyn Diagnostic>) -> String {
        format!(
            "{}: {}\n{}",
            err.code(),
            err.message(),
            self.format_span(err.main_span())
        )
    }

    /// This implementation is entirely provisional! In particular, newlines
    /// aren't tracked by the scanner. Instead finding line breaks in any
    /// remotely intelligent way, we'll simply scan forward and backward until
    /// hitting them.
    fn format_span(&self, span: &Span) -> String {
        let src = self.get(&span.src_id).unwrap();
        // FIXME assume for now that spans don't cross lines
        let line = src.get_line(span.start);
        // Columns to annotate: remember that columns are 1-indexed.
        let start = span.start.col;
        let end = span.end.col;
        // Carets
        let annot = "^".repeat(end - start + 1);
        // How long should line numbers be?
        let digits = count_digits(span.start.line);
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

#[derive(Debug)]
enum SrcKind {
    /// A source file
    File { code: String, file: PathBuf },
    /// Interactive input, not from any file, possibly with multiple lines
    Input { code: String },
}

// Instead of implementing these methods here, you might consider implementing
// them on a SourceObject, and having that hold a SrcKind or reference to a
// SrcKind. This does run into some ugly lifetime issues, though.
impl SrcKind {
    /// Get a view of the source code
    pub fn code(&self) -> &str {
        match &self {
            SrcKind::File { code, .. } => code,
            SrcKind::Input { code } => code,
        }
    }

    /// Get the origin of the source code
    pub fn origin(&self) -> &str {
        match &self {
            // TODO Is this unwrap safe?
            SrcKind::File { file, .. } => file.as_path().to_str().unwrap(),
            SrcKind::Input { .. } => "<input>",
        }
    }
}

/// A character point within a file. Note that this is extremely uneconomical:
/// three `usize`s make this struct occupy 24 bytes. This could be done a little
/// more efficiently by having the parser cleverly mark newlines and so on in an
/// auxiliary data structure associated with each source object.
#[derive(Debug, Default, Eq, PartialEq, PartialOrd, Ord, Clone, Copy)]
pub struct SrcPoint {
    /// Position in source file: because derived PartialOrd and Ord use
    /// lexicographical ordering based on the declaration order of the struct
    /// members, this member alone will be compared in practice.
    pub pos: usize,
    /// Line number in source file
    pub line: usize,
    /// Column number in source file
    pub col: usize,
}

impl SrcPoint {
    pub fn zero() -> Self {
        Self::default()
    }
}

/// Span within a single source file. This plays basically the same role as a
/// `Span` in rustc, but the data structure is much simpler.
#[derive(Debug, Default, Eq, PartialEq, Clone, Copy)]
pub struct Span {
    /// First character point in the span
    pub start: SrcPoint,
    /// End, _inclusive_
    pub end: SrcPoint,
    /// Containing source object id
    pub src_id: SrcId,
}

impl Span {
    /// Join two spans, as in the diagram below:
    ///
    /// ```text
    /// [------]   [--]
    ///        V
    /// [-------------]
    /// ```
    ///
    /// If the spans come from separate files, there's no meaningful way to
    /// order them, so this function is partial.
    pub fn join(&self, other: &Span) -> Option<Span> {
        if self.src_id != other.src_id {
            None
        } else {
            let start = std::cmp::min(self.start, other.start);
            let end = std::cmp::max(self.start, other.end);
            Some(Span {
                start,
                end,
                src_id: self.src_id,
            })
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.start.line == self.end.line {
            write!(
                f,
                "[{}:{}-{}]",
                self.start.line, self.start.pos, self.end.pos
            )
        } else {
            write!(
                f,
                "[{}:{}]-[{}:{}]",
                self.start.line, self.start.pos, self.end.line, self.end.pos
            )
        }
    }
}

#[cfg(test)]
mod tests {}
