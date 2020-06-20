use std::fmt;

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType {
    // identifiers
    Ident(String),

    // keywords
    If, Else, For, Fn, Reg, Print,

    // literals
    Int(u32), True, False,

    // two-character token types
    StopStop, EqualEqual, TildeEqual, LessMinus,

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
    pub len: usize,  // length of the token
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
