/// Data strucures for holding and manipulating source code
use crate::errors::ErrorBuf;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::path::PathBuf;

/// Unique identifier of a source object. I'll be surprised if anyone ever needs more
/// than two bytes to identify all of their source objects.
pub type SrcId = u16;

/// Type returned by the public SrcStore interface. This is expected to be
/// passed to a Scanner.
pub struct SrcObject<'src> {
    /// ID of the source object, used for reporting errors.
    pub id: SrcId,
    /// View of the source as a string
    pub code: &'src str,
}

impl<'s> From<&'s str> for SrcObject<'s> {
    fn from(code: &'s str) -> Self {
        Self { id: 0, code }
    }
}

/// Store of all the source objects loaded by the compiler. We're using a
/// HashMap with a SrcId key, rather than a Vec, to save space. Every node in
/// the AST will contain a SrcId, so they better be economical.
#[derive(Default)]
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
    pub fn insert_path(&mut self, path: PathBuf) -> Result<Option<SrcObject>, ErrorBuf> {
        let src_file = SrcKind::try_from(path)?;
        let id = self.new_id();
        self.table.insert(id, src_file);
        // FIXME defeating the borrow checker...
        Ok(self.get(&id))
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
            code: src.as_src(),
        })
    }
}

enum SrcKind {
    /// A source file
    File { code: String, file: PathBuf },
    /// Interactive input, not from any file, possibly with multiple lines
    Input { code: String },
}

impl SrcKind {
    /// Get a view of the source code
    fn as_src(&self) -> &str {
        match self {
            SrcKind::File { code, .. } => code,
            SrcKind::Input { code } => code,
        }
    }
}

impl TryFrom<PathBuf> for SrcKind {
    type Error = ErrorBuf;

    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        let code = match std::fs::read_to_string(&path) {
            Ok(code) => code,
            Err(err) => {
                return Err(ErrorBuf(vec![Box::new(err)]));
            }
        };

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
#[derive(Debug, Default, Eq, PartialEq, PartialOrd, Ord, Clone)]
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
#[derive(Debug, Default, Eq, PartialEq, Clone)]
pub struct Span {
    /// First character point in the span
    pub start: SrcPoint,
    /// End, _inclusive_
    pub end: SrcPoint,
    /// Containing source object id
    pub src_id: SrcId,
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
