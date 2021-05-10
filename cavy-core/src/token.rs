use crate::{
    context::{self, Context, SymbolId},
    num::Uint,
    source::{Span, SrcObject},
    util::FmtWith,
};
use std::fmt;

pub type Unsigned = u32;

#[rustfmt::skip]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Lexeme {
    // identifiers
    Ident(SymbolId),

    // `'a`,...
    Tick(SymbolId),

    // keywords
    If, Else, Match, For, Let, Mut, In, Fn, FFn, Type, Struct,
    Enum, Impl, Io, True, False, Bool, U2, U4, U8, U16, U32, Ord,
    Unsafe, Assert, Drop,

    // literals
    Nat(Unsigned, Option<Uint>),

    // two-character token types
    DotDot, EqualEqual, TildeEqual, MinusRAngle, EqualRAngle,
    ColonColon, VertVert, AmpAmp, VertEqual, AmpEqual, CarotEqual,

    // single-character token types
    Dot, Equal, Plus, Minus, Star, Percent, Bang, Question, Tilde,
    Comma, Semicolon, Colon, LAngle, RAngle, Octothorpe, Ampersand,
    Dollar, Carot,

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

impl<'c> FmtWith<Context<'c>> for Lexeme {
    fn fmt(&self, ctx: &context::Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lexeme::Ident(s) => write!(f, "{}", s.fmt_with(ctx)),
            Lexeme::Tick(s) => write!(f, "'{}", s.fmt_with(ctx)),
            other => write!(f, "{}", other),
        }
    }
}

impl fmt::Display for Lexeme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Delim::*;
        use Lexeme::*;
        let s = match self {
            Ident(_) => "<ident>",
            Tick(_) => "<lt>",
            Fn => "fn",
            FFn => "Fn",
            For => "for",
            Let => "let",
            Mut => "mut",
            In => "in",
            Bool => "bool",
            U2 => "u2",
            U4 => "u4",
            U8 => "u8",
            U16 => "u16",
            U32 => "u32",
            Nat(nat, sz) => {
                let _ = write!(f, "{}", nat);
                if let Some(sz) = sz {
                    let _ = write!(f, "{}", sz);
                }
                return Ok(());
            }
            Dot => ".",
            DotDot => "..",
            EqualEqual => "==",
            VertVert => "||",
            AmpAmp => "&&",
            Carot => "^",
            TildeEqual => "~=",
            MinusRAngle => "->",
            EqualRAngle => "=>",
            ColonColon => "::",
            Equal => "=",
            VertEqual => "|=",
            AmpEqual => "&=",
            CarotEqual => "^=",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Dollar => "$",
            Percent => "%",
            Bang => "!",
            Tilde => "~",
            Octothorpe => "#",
            Ampersand => "&",
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
            Enum => "enum",
            Impl => "impl",
            Io => "io",
            True => "true",
            False => "false",
            Question => "?",
            Ord => "ord",
            Unsafe => "unsafe",
            Assert => "assert",
            Drop => "drop",
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
    pub name: SymbolId,
    pub span: Span,
}
