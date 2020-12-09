use std::fmt;
use std::path::PathBuf;

pub type Unsigned = u32;

#[rustfmt::skip]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Lexeme {
    // identifiers
    Ident(String),

    // keywords
    If, Else, For, Let, In, Fn, Print, True, False,
    Bool, U4, U8, U16, U32,

    // literals
    Nat(Unsigned),

    // two-character token types
    DotDot, EqualEqual, TildeEqual,

    // single-character token types
    Equal, Plus, Minus, Star, Percent, Bang, Question, Tilde, Comma, Semicolon,
    Colon,

    // delimiters
    LBracket, RBracket, LParen, RParen, LBrace, RBrace, LAngle, RAngle,
}

impl fmt::Display for Lexeme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Lexeme::*;
        let repr = match self {
            Ident(s) => s.clone(),
            Fn => "fn".to_owned(),
            For => "for".to_owned(),
            Let => "let".to_owned(),
            In => "in".to_owned(),
            Nat(nat) => format!("{}", nat),
            DotDot => "..".to_owned(),
            EqualEqual => "==".to_owned(),
            TildeEqual => "~=".to_owned(),
            Plus => "+".to_owned(),
            Minus => "-".to_owned(),
            Star => "*".to_owned(),
            Percent => "%".to_owned(),
            Bang => "!".to_owned(),
            Tilde => "~".to_owned(),
            LParen => "(".to_owned(),
            RParen => ")".to_owned(),
            LBracket => "[".to_owned(),
            RBracket => "]".to_owned(),
            LBrace => "{".to_owned(),
            RBrace => "}".to_owned(),
            _ => "?".to_string(),
        };
        write!(f, "{}", repr)
    }
}

#[derive(Debug, Default, Eq, PartialEq, Clone)]
pub struct Location {
    pub pos: usize,  // starting position in source file
    pub line: usize, // line number in source file
    pub col: usize,  // column number in source file
    pub file: Option<PathBuf>,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.file {
            Some(file) => write!(f, "{}:{} ({:?})", self.col, self.line, file),
            None => write!(f, "{}:{} (input)", self.col, self.line),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Token {
    pub lexeme: Lexeme,
    pub loc: Location,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.lexeme)
    }
}
