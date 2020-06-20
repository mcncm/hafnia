use std::fmt;
use std::path::PathBuf;

pub type Unsigned = u32;

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lexeme {
    // identifiers
    Ident(String),

    // keywords
    If, Else, For, Let, Fn, Print, True, False,

    // literals
    Nat(Unsigned),

    // two-character token types
    StopStop, EqualEqual, TildeEqual,

    // single-character token types
    Plus, Star, Bang, QuestionMark, Tilde, Comma, Semicolon,

    // delimiters
    LBracket, RBracket, LParen, RParen, LBrace, RBrace,

    // end of file
    Eof,
}

impl fmt::Display for Lexeme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repr = match self {
            Self::Ident(s) => s.clone(),
            Self::Nat(nat) => format!("{}", nat),
            Self::StopStop => "..".to_owned(),
            Self::EqualEqual => "==".to_owned(),
            Self::TildeEqual => "~=".to_owned(),
            Self::Plus => "+".to_owned(),
            Self::Star => "*".to_owned(),
            Self::Bang => "!".to_owned(),
            Self::Tilde => "~".to_owned(),
            _ => "?".to_string(),
        };
        write!(f, "{}", repr)
    }
}

#[derive(Debug)]
pub struct Location {
    pub pos: usize,  // starting position in source file
    pub line: usize, // line number in source file
    pub col: usize,  // column number in source file
    pub file: Option<String>,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.file {
            Some(file) => write!(f, "{}:{} ({:?})", self.col, self.line, file),
            None => write!(f, "{}:{} (input)", self.col, self.line),
        }
    }
}

#[derive(Debug)]
pub struct Token {
    pub lexeme: Lexeme,
    pub loc: Location,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.lexeme)
    }
}
