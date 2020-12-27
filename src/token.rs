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
    Nat(Unsigned),

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
        let repr = match self {
            Ident(s) => s.clone(),
            Fn => "fn".to_owned(),
            For => "for".to_owned(),
            Let => "let".to_owned(),
            In => "in".to_owned(),
            Bool => "bool".to_owned(),
            U8 => "u8".to_owned(),
            U16 => "u16".to_owned(),
            U32 => "u32".to_owned(),
            Nat(nat) => format!("{}", nat),
            DotDot => "..".to_owned(),
            EqualEqual => "==".to_owned(),
            TildeEqual => "~=".to_owned(),
            MinusRAngle => "->".to_owned(),
            Equal => "=".to_owned(),
            Plus => "+".to_owned(),
            Minus => "-".to_owned(),
            Star => "*".to_owned(),
            Percent => "%".to_owned(),
            Bang => "!".to_owned(),
            Tilde => "~".to_owned(),
            Comma => ",".to_owned(),
            Semicolon => ";".to_owned(),
            Colon => ":".to_owned(),
            LParen => "(".to_owned(),
            RParen => ")".to_owned(),
            LBracket => "[".to_owned(),
            RBracket => "]".to_owned(),
            LBrace => "{".to_owned(),
            RBrace => "}".to_owned(),
            LAngle => "<".to_owned(),
            RAngle => ">".to_owned(),
            _ => "?".to_string(),
        };
        write!(f, "{}", repr)
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
