use std::fmt;

pub type Unsigned = u32;

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType {
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

#[derive(Debug)]
pub struct Location {
    pub pos: usize,  // starting position in source file
    pub line: usize, // line number in source file
    pub col: usize,  // column number in source file
}

pub struct Token {
    pub token_type: TokenType,
    pub loc: Location,
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("").field(&self.token_type).finish()
    }
}
