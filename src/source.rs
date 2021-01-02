//! Data strucures for holding and manipulating source code

use crate::cavy_errors::{Diagnostic, ErrorBuf};
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

/// Unique identifier of a source object. I'll be surprised if anyone ever needs more
/// than two bytes to identify all of their source objects.
pub type SrcId = u16;

/// Type returned by the public SrcStore interface. This is expected to be
/// passed to a Scanner.
pub struct SrcObject<'src> {
    /// ID of the source object, used for reporting errors
    pub id: SrcId,
    /// The locations of newline characters within the source object: filled in
    /// by the scanner
    pub newlines: Vec<usize>,
    pub code: &'src str,
    pub origin: &'src str,
}

impl<'s> SrcObject<'s> {
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
    fn get_line(&self, pos: SrcPoint) -> &'s str {
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
            n => self.newlines[n - 1] + 1,
        };

        // line end
        let ln_end = if n == self.newlines.len() {
            self.code.len()
        } else {
            self.newlines[n]
        };

        &self.code[ln_start..ln_end]
    }
}

impl From<&'static str> for SrcObject<'_> {
    fn from(code: &'static str) -> Self {
        Self {
            id: 0,
            code,
            origin: "<static>",
            newlines: vec![],
        }
    }
}

/// Store of all the source objects loaded by the compiler. We're using a
/// HashMap with a SrcId key, rather than a Vec, to save space. Every node in
/// the AST will contain a SrcId, so they better be economical.
#[derive(Default, Debug)]
pub struct SrcStore {
    next_id: SrcId,
    table: HashMap<SrcId, SrcKind>,
}

impl SrcStore {
    pub fn new() -> Self {
        Self {
            // Start at 1 so 0 can be used as a special value for SourceObjects
            // not derived from a store
            next_id: 1,
            table: HashMap::new(),
        }
    }
}

impl SrcStore {
    fn new_id(&mut self) -> SrcId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Try to insert a path to a source file and retrieve a source object
    pub fn insert_path(&mut self, path: PathBuf) -> Result<SrcId, std::io::Error> {
        // FIXME handle this error a bit better.
        let src_file = SrcKind::try_from(path)?;
        let id = self.new_id();
        self.table.insert(id, src_file);
        // FIXME defeating the borrow checker...
        Ok(id)
    }

    pub fn insert_input(&mut self, input: &str) -> SrcObject {
        let id = self.new_id();
        let input = SrcKind::Input {
            code: input.to_owned(),
        };
        self.table.insert(id, input);
        // FIXME defeating the borrow checker...
        self.get(&id).unwrap()
    }

    /// Retrieve source code from the store of source objects
    pub fn get(&self, id: &SrcId) -> Option<SrcObject> {
        self.table.get(id).map(|src| SrcObject {
            id: *id,
            code: src.code(),
            origin: src.origin(),
            newlines: vec![],
        })
    }

    pub fn format_err(&self, err: &dyn Diagnostic) -> String {
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
        // really be some kind of "join".
        let origin = format!("{}:{}:{}-{}", src.origin, span.start.line, start, end);
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

impl TryFrom<PathBuf> for SrcKind {
    type Error = std::io::Error;

    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        let code = std::fs::read_to_string(&path)?;

        let src = Self::File {
            code,
            // FIXME This should be a PathBuf, but there were some difficulties
            // with lifetimes last time I tried to do that.
            file: path,
        };

        Ok(src)
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
