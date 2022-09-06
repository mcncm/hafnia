//! Data strucures for holding and manipulating source code

use crate::hafnia_errors::{Diagnostic, ErrorBuf};
use crate::store_type;
use std::convert::TryFrom;
use std::fmt;
use std::path::PathBuf;
use std::{collections::HashMap, str::Chars};

// /// Unique identifier of a source object. I'll be surprised if anyone ever needs more
// /// than two bytes to identify all of their source objects.
store_type! { SrcStore : SrcId -> SrcObject }

pub struct SrcLine<'a> {
    /// The substring of the line in question
    pub code: &'a str,
    /// 1-indexed line number
    pub linum: std::num::NonZeroUsize,
    /// Start byte position
    pub start: usize,
    /// End byte position
    pub end: usize,
}

impl<'a> SrcLine<'a> {
    pub fn chars(&self) -> Chars<'a> {
        self.code.chars()
    }
}

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
    /// Get the zero-indexed line number
    pub fn line_index(&self, pos: SrcPoint) -> usize {
        // Pointing to a newline character shouldn't happen; actual spans
        // shouldn't point *at* newlines, but they might cross them.
        self.newlines
            .binary_search(&pos)
            .expect_err("SrcPoint pointed at newline")
    }

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
    pub fn get_line(&self, pos: SrcPoint) -> SrcLine<'_> {
        let line_idx = self.line_index(pos);
        // line start: inclusive if pointing to first line, exclusive
        // otherwise (to exclude newline character)
        let start = match line_idx {
            0 => 0,
            n => self.newlines[n - 1] + 1,
        };

        // line end
        let end = if line_idx == self.newlines.len() {
            self.code.len()
        } else {
            self.newlines[line_idx]
        };

        let linum = std::num::NonZeroUsize::new(line_idx + 1).unwrap();

        SrcLine {
            code: &self.code[start..end],
            linum,
            start,
            end,
        }
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

/// A character point within a file.
pub type SrcPoint = usize;

/// Span within a single source file. This plays basically the same role as a
/// `Span` in rustc, but the data structure is much simpler.
#[derive(Debug, Default, Eq, PartialEq, Hash, Clone, Copy)]
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

    pub fn first_point(&self) -> Span {
        Span {
            start: self.start,
            end: self.start,
            src_id: self.src_id,
        }
    }

    pub fn last_point(&self) -> Span {
        Span {
            start: self.end,
            end: self.end,
            src_id: self.src_id,
        }
    }
}

impl fmt::Display for SrcObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.origin)
    }
}

impl<'a> fmt::Display for SrcLine<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.code)
    }
}
