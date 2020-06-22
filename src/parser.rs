use crate::ast::Expr;
use crate::errors;
use crate::token::{
    Lexeme::{self, *},
    Location, Token,
};
use lazy_static::lazy_static;
use std::collections::HashMap;
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

struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    errors: Vec<ParseError>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: vec![],
        }
    }

    fn peek_lexeme(&mut self) -> Option<&Lexeme> {
        self.tokens.peek().map(|tok| &tok.lexeme)
    }

    #[allow(unused_mut)]
    fn parse(mut self) -> Result<Expr, ParseError> {
        todo!();
    }

    fn expression(&mut self) -> Result<Expr, ParseError> {
        let lhs = self.unary()?;
        self.precedence_climb(lhs, 0)
    }

    fn unary(&mut self) -> Result<Expr, ParseError> {
        if let Some(Bang) | Some(Tilde) = self.peek_lexeme() {
            let op = self.tokens.next().unwrap();
            let right = self.unary()?;
            return Ok(Expr::UnOp {
                op,
                right: Box::new(right),
            });
        }
        self.terminal()
    }

    fn terminal(&mut self) -> Result<Expr, ParseError> {
        match self.peek_lexeme().unwrap() {
            Nat(_) | True | False => Ok(Expr::Literal(self.tokens.next().unwrap())),
            Ident(_) => Ok(Expr::Variable(self.tokens.next().unwrap())),
            _ => {
                todo!();
            }
        }
    }

    fn precedence_climb(&self, _lhs: Expr, _min_precedence: u8) -> Result<Expr, ParseError> {
        todo!();
    }

    fn synchronize(&mut self, _err: &str) {
        todo!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Expr::{self, *};
    use crate::token::Token;
    use Lexeme::*;

    // macro_rules! token {
    //     ($lexeme:expr) => {
    //         Token {
    //             lexeme: $lexeme,
    //             loc: Location::default(),
    //         }
    //     }
    // }

    fn token(lexeme: Lexeme) -> Token {
        Token {
            lexeme,
            loc: Location::default(),
        }
    }

    fn literal(lexeme: Lexeme) -> Expr {
        Literal(token(lexeme))
    }

    fn variable(lexeme: Lexeme) -> Expr {
        Variable(token(lexeme))
    }

    /// We'll use this macro to test the parser. The parse tree templates will
    /// take the form of S-expressions parenthesizes with curly braces (for
    /// readability), with leaves being calls to the `token`, `literal`, and
    /// `variable` functions.
    macro_rules! test_s_expr {
        // Literal
        ($ast:expr, literal($lexeme:expr)) => {
            assert_eq!($ast, literal($lexeme));
        };
        // Variable
        ($ast:expr, variable($lexeme:expr)) => {
            assert_eq!($ast, variable($lexeme));
        };
        // UnOp
        ($ast:expr, {token($op:ident) $($right:tt)+}) => {
            match $ast {
                UnOp { op, right } => {
                    assert_eq!(op, token($op));
                    test_s_expr! { *right, $($right)+ };
                },
                _ => { panic!(); },
            }
        };
        // BinOp
        //($ast:ident (BinOp $left:tt $right:tt)) => {

        //}
    }

    macro_rules! test_parser {
        // $leaf needs this peculiar structure, and cannot be an `expr`, because
        // it would otherwise capture its own output and recurse forever.
        ([$($lexeme:expr),+], $($s_expr:tt)+) => {
            let tokens = vec![$(token($lexeme)),+];
            let mut parser = Parser::new(tokens);
            let ast = parser.unary().unwrap();
            test_s_expr!(ast, $($s_expr)+);
        };
    }

    #[test]
    fn token_macro() {
        let token = token(Nat(1));
        assert_eq!(
            token,
            Token {
                lexeme: Nat(1),
                loc: Location::default()
            }
        );
    }

    #[test]
    fn single_nat_1() {
        test_parser! {
            [Nat(1)],
            literal(Nat(1))
        };
    }

    #[test]
    #[should_panic]
    fn single_nat_2() {
        test_parser! {
            [Nat(0)],
            literal(Nat(1))
        };
    }

    #[test]
    fn single_false() {
        test_parser! {
            [False],
            literal(False)
        }
    }

    #[test]
    fn single_true() {
        test_parser! {
            [True],
            literal(True)
        }
    }

    #[test]
    fn single_var_1() {
        let name = "foo";
        test_parser! {
            [Ident(name.to_owned())],
            variable(Ident(name.to_owned()))
        };
    }

    #[test]
    #[should_panic]
    fn single_var_2() {
        test_parser! {
            [Ident("foo".to_owned())],
            variable(Ident("bar".to_owned()))
        };
    }

    #[test]
    fn tilde_false() {
        test_parser! {
            [Tilde, False],
            {token(Tilde) literal(False)}
        }
    }

    #[test]
    fn bang_false() {
        test_parser! {
            [Bang, False],
            {token(Bang) literal(False)}
        }
    }

    #[test]
    fn tilde_tilde_false() {
        test_parser! {
            [Tilde, Tilde, False],
            {token(Tilde) {token(Tilde) literal(False)}}
        }
    }

    #[test]
    fn tilde_bang_false() {
        test_parser! {
            [Tilde, Tilde, False],
            {token(Tilde) {token(Tilde) literal(False)}}
        }
    }
}
