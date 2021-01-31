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
    If, Else, For, Let, In, Fn, Print, True, False,
    Bool, U4, U8, U16, U32,

    // literals
    Nat(Unsigned, Option<Uint>),

    // two-character token types
    DotDot, EqualEqual, TildeEqual, MinusRAngle,

    // single-character token types
    Equal, Plus, Minus, Star, Percent, Bang, Question, Tilde, Comma, Semicolon,
    Colon,

    // delimiters
    LBracket, RBracket, LParen, RParen, LBrace, RBrace, LAngle, RAngle,
}

impl fmt::Display for Lexeme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Lexeme::*;
        match self {
            Ident(s) => write!(f, "{}", s),
            Fn => f.write_str("fn"),
            For => f.write_str("for"),
            Let => f.write_str("let"),
            In => f.write_str("in"),
            Bool => f.write_str("bool"),
            U8 => f.write_str("u8"),
            U16 => f.write_str("u16"),
            U32 => f.write_str("u32"),
            Nat(nat, sz) => {
                let _ = write!(f, "{}", nat);
                if let Some(sz) = sz {
                    let _ = write!(f, "{}", sz);
                }
                f.write_str("")
            }
            DotDot => f.write_str(".."),
            EqualEqual => f.write_str("=="),
            TildeEqual => f.write_str("~="),
            MinusRAngle => f.write_str("->"),
            Equal => f.write_str("="),
            Plus => f.write_str("+"),
            Minus => f.write_str("-"),
            Star => f.write_str("*"),
            Percent => f.write_str("%"),
            Bang => f.write_str("!"),
            Tilde => f.write_str("~"),
            Comma => f.write_str(","),
            Semicolon => f.write_str(";"),
            Colon => f.write_str(":"),
            LParen => f.write_str("("),
            RParen => f.write_str(")"),
            LBracket => f.write_str("["),
            RBracket => f.write_str("]"),
            LBrace => f.write_str("{"),
            RBrace => f.write_str("}"),
            LAngle => f.write_str("<"),
            RAngle => f.write_str(">"),
            _ => f.write_str("?"),
        }
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
