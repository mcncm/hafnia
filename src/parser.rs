use crate::ast::Expression;
use crate::errors;
use crate::token::{Lexeme, Location, Token};
use std::fmt;
use std::iter::Peekable;
use std::vec::IntoIter;

#[derive(Debug)]
pub struct ParseError {
    msg: &'static str,
    tokens: Vec<Token>,
}

impl fmt::Display for ParseError {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Parsing error [{}]: {}",
              self.tokens[0].loc, self.msg
        )
    }
}

impl errors::Error for ParseError {}

struct ParseHead {
    tokens: Peekable<IntoIter<Token>>,
}

impl ParseHead {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
        }
    }

    fn next(&mut self) -> Option<Token> {
        self.tokens.next()
    }
}

struct Parser {
    parse_head: ParseHead,
    errors: Vec<ParseError>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            parse_head: ParseHead::new(tokens),
            errors: vec![],
        }
    }

    #[allow(unused_mut)]
    fn parse(mut self) -> Result<Expression, ParseError> {
        todo!();
    }

    fn terminal(&mut self) -> Result<Expression, ParseError> {
        todo!();
        // match self.tokens.next() {
        //     Some(token) => match {
        //
        //     },
        //     None =>
        //     Some(Token { lexeme: Lexeme::Ident(s), loc: _ }) => Ok(Lexeme::Ident(s)),
        //     Some(Lexeme::Nat(n)) => Ok(Lexeme::Nat(s)),
        // }
    }

    fn synchronize(&mut self, _err: &str) {
        todo!();
        // let
        // for token in self.parse_head { }  // for now, go to end of tokens
        // self.errors.push(err);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
