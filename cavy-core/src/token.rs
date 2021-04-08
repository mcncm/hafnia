use crate::num::Uint;
use crate::source::Span;
use crate::source::SrcObject;
use std::fmt;

pub type Unsigned = u32;

#[rustfmt::skip]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Lexeme {
    // identifiers
    Ident(String),

    // keywords
    If, Else, Match, For, Let, In, Fn, Type, Struct, Print, True, False,
    Bool, U4, U8, U16, U32, Ord,

    // literals
    Nat(Unsigned, Option<Uint>),

    // two-character token types
    DotDot, EqualEqual, TildeEqual, MinusRAngle, EqualRAngle,

    // single-character token types
    Dot, Equal, Plus, Minus, Star, Percent, Bang, Question, Tilde,
    Comma, Semicolon, Colon, LAngle, RAngle,

    // delimiters
    LDelim(Delim), RDelim(Delim),
}

/// Kinds of delimiters: `(`/`)`, `[`/`]`, `{`/`}`
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Delim {
    Paren,
    Bracket,
    Brace,
}

impl fmt::Display for Lexeme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Delim::*;
        use Lexeme::*;
        let s = match self {
            Ident(s) => return write!(f, "{}", s),
            Fn => "fn",
            For => "for",
            Let => "let",
            In => "in",
            Bool => "bool",
            U8 => "u8",
            U16 => "u16",
            U32 => "u32",
            Nat(nat, sz) => {
                let _ = write!(f, "{}", nat);
                if let Some(sz) = sz {
                    let _ = write!(f, "{}", sz);
                }
                return f.write_str("");
            }
            Dot => ".",
            DotDot => "..",
            EqualEqual => "==",
            TildeEqual => "~=",
            MinusRAngle => "->",
            EqualRAngle => "=>",
            Equal => "=",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Percent => "%",
            Bang => "!",
            Tilde => "~",
            Comma => ",",
            Semicolon => ";",
            Colon => ":",
            LDelim(Paren) => "(",
            RDelim(Paren) => ")",
            LDelim(Bracket) => "[",
            RDelim(Bracket) => "]",
            LDelim(Brace) => "{",
            RDelim(Brace) => "}",
            LAngle => "<",
            RAngle => ">",
            If => "if",
            Match => "match",
            Else => "else",
            Type => "type",
            Struct => "struct",
            Print => "print",
            True => "true",
            False => "false",
            U4 => "u4",
            Question => "?",
            Ord => "ord",
        };
        f.write_str(s)
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Token {
    pub lexeme: Lexeme,
    pub span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.lexeme)
    }
}

/// It is terribly useful for the AST to contain Ident structs without
/// necessitating an extra `match`. Breaking this out saves a lot of indentation
/// depth elsewhere in this code.
#[derive(Debug, Clone)]
pub struct Ident {
    /// The actual name associated with the identifier
    pub name: String,
    pub span: Span,
}
