use crate::ast::{Expr, Stmt};
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

/// Operator precedence: the first field is the scalar precedence; the second is
/// its right associativity.
struct Precedence(u8, bool);

lazy_static! {
    #[rustfmt::skip]
    static ref OPERATOR_TABLE: HashMap<Lexeme, Precedence> = {
        let mut m = HashMap::new();
        m.insert(TildeEqual, Precedence(0, false));
        m.insert(EqualEqual, Precedence(0, false));
        m.insert(LAngle,     Precedence(1, false));
        m.insert(RAngle,     Precedence(1, false));
        m.insert(Plus,       Precedence(2, false));
        m.insert(Star,       Precedence(3, false));
        m
    };
}

#[derive(Debug)]
pub struct ParseError {
    msg: &'static str,
    token: Option<Token>,
}

impl fmt::Display for ParseError {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.token {
            Some(token) => {
                write!(f, "Parsing error at \"{}\" [{}]: {}",
                       token, token.loc, self.msg)
            } ,
            None => {
                write!(f, "Parsing error: {}", self.msg)
            }
        }
    }
}

impl std::error::Error for ParseError {}

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    errors: Vec<ParseError>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: vec![],
        }
    }

    fn peek_lexeme(&mut self) -> Option<&Lexeme> {
        self.tokens.peek().map(|token| &token.lexeme)
    }

    fn forward(&mut self) {
        self.tokens.next();
    }

    /// Consumes the parser, generating a list of statements
    pub fn parse(mut self) -> Result<Vec<Stmt>, ParseError> {
        let mut stmts = vec![];
        while let Some(stmt) = self.declaration()? {
            stmts.push(stmt);
        }
        Ok(stmts)
    }

    fn consume(&mut self, lexeme: Lexeme, msg: &'static str) -> Result<Token, ParseError> {
        let token = self.tokens.next().ok_or(ParseError {
            msg: "No token found",
            token: None,
        })?;
        if token.lexeme == lexeme {
            return Ok(token);
        }
        Err(ParseError {
            msg,
            token: Some(token),
        })
    }

    pub fn statement(&mut self) -> Result<Option<Stmt>, ParseError> {
        let stmt = match self.peek_lexeme() {
            Some(Print) => self.print_stmt(),
            Some(Let) => self.assn_stmt(),
            Some(For) => self.for_stmt(),
            None => {
                return Ok(None);
            }
            _ => self.expr_stmt(),
        };
        match stmt {
            Ok(stmt) => Ok(Some(stmt)),
            Err(err) => Err(err),
        }
    }

    pub fn declaration(&mut self) -> Result<Option<Stmt>, ParseError> {
        // TODO Check for assignment
        // TODO Check for function definition
        self.statement()
    }

    fn assn_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.forward();
        let lhs = Box::new(self.expression()?);
        self.consume(Lexeme::Equal, "missing '=' in assignment")?;
        let rhs = Box::new(self.expression()?);
        self.consume(Lexeme::Semicolon, "missing ';' after assignment")?;
        Ok(Stmt::Assn { lhs, rhs })
    }

    fn print_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.forward();
        let expr = self.expression()?;
        self.consume(Lexeme::Semicolon, "missing ';' after statement")?;
        Ok(Stmt::Print(Box::new(expr)))
    }

    fn if_expr(&mut self) -> Result<Expr, ParseError> {
        self.forward();
        // Here we assume that
        let cond = Box::new(self.expression()?);
        self.consume(
            Lexeme::LBrace,
            "expected '{' opening direct branch of conditional.",
        )?;
        let then_branch = Box::new(self.block_expr()?);
        self.consume(Lexeme::Else, "expected 'else' in conditional expression")?;
        self.consume(
            Lexeme::LBrace,
            "expected '{' opening indirect branch of conditional.",
        )?;
        let else_branch = Box::new(self.block_expr()?);

        Ok(Expr::If {
            cond,
            then_branch,
            else_branch,
        })
    }

    fn for_stmt(&mut self) -> Result<Stmt, ParseError> {
        todo!();
    }

    fn block_expr(&mut self) -> Result<Expr, ParseError> {
        let mut stmts = vec![];
        while let Some(lexeme) = self.peek_lexeme() {
            if lexeme == &Lexeme::RBrace {
                break;
            }
            stmts.push(self.declaration()?.unwrap())
        }
        self.consume(Lexeme::RBrace, "missing '}' at end of block")?;

        // The final expression of the block: we’ll handle this for now by
        // saying that if the final statement is an expression statement,
        // remove it and use it as the final value.
        let mut final_expr = None;
        match stmts.pop() {
            Some(Stmt::Expr(expr)) => {
                final_expr = Some(expr);
            }
            Some(stmt) => {
                // Put it back
                stmts.push(stmt);
            }
            None => {}
        }
        Ok(Expr::Block(stmts, final_expr))
    }

    fn expr_stmt(&mut self) -> Result<Stmt, ParseError> {
        Ok(Stmt::Expr(Box::new(self.expression()?)))
    }

    pub fn expression(&mut self) -> Result<Expr, ParseError> {
        match self.peek_lexeme() {
            Some(Lexeme::If) => self.if_expr(),
            Some(Lexeme::LBrace) => self.block_expr(),
            Some(_) => {
                let lhs = self.unary()?;
                self.precedence_climb(lhs, 0)
            }
            _ => unreachable!(),
        }
    }

    fn unary(&mut self) -> Result<Expr, ParseError> {
        if let Some(Bang) | Some(Tilde) | Some(Question) = self.peek_lexeme() {
            let op = self.tokens.next().unwrap();
            let right = self.unary()?;
            return Ok(Expr::UnOp {
                op,
                right: Box::new(right),
            });
        }
        self.primary()
    }

    fn primary(&mut self) -> Result<Expr, ParseError> {
        match self.peek_lexeme().unwrap() {
            Nat(_) | True | False => Ok(Expr::Literal(self.tokens.next().unwrap())),
            Ident(_) => Ok(Expr::Variable(self.tokens.next().unwrap())),
            LParen => {
                self.forward();
                let expr = self.expression();
                self.consume(RParen, "Expected closing paren ')'")?;
                Ok(Expr::Group(Box::new(expr?)))
            }
            _ => Err(ParseError {
                token: self.tokens.next(),
                msg: "not a primary token.",
            }),
        }
    }

    fn precedence_climb(&mut self, lhs: Expr, min_precedence: u8) -> Result<Expr, ParseError> {
        let mut lhs = lhs;
        let mut op_prec;
        while let Some(outer) = self.peek_lexeme() {
            // Check the outer operator's precedence
            if let Some(Precedence(outer_prec, _)) = OPERATOR_TABLE.get(outer) {
                op_prec = *outer_prec;
                if op_prec < min_precedence {
                    break;
                }
                let outer = self.tokens.next().unwrap();
                let mut rhs = self.unary()?;
                while let Some(inner) = self.peek_lexeme() {
                    // Check the inner operator's precedence
                    if let Some(Precedence(inner_prec, r_assoc)) = OPERATOR_TABLE.get(inner) {
                        if inner_prec + (*r_assoc as u8) <= op_prec {
                            break;
                        }
                        rhs = self.precedence_climb(rhs, *inner_prec)?;
                    } else {
                        break;
                    }
                }
                lhs = Expr::BinOp {
                    op: outer,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                };
            } else {
                break;
            }
        }
        Ok(lhs)
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

    //////////////////////////////////////////////////////
    // Functions and macros for constructing test cases //
    //////////////////////////////////////////////////////

    fn token(lexeme: Lexeme) -> Token {
        Token {
            lexeme,
            loc: Location::default(),
        }
    }

    /// We'll use this macro to test the parser. The parse tree templates will
    /// take the form of S-expressions. Two avoid wrangling with the Rust macro
    /// system more than necessary, the leaves of the S-expressions must be
    /// enclosed in curly braces.
    macro_rules! test_s_expr {
        // BinOp
        ($ast:expr, ({$op:expr} $left:tt $right:tt)) => {
            match $ast {
                BinOp { op, left, right } => {
                    assert_eq!(op.lexeme, $op);
                    test_s_expr! { *left, $left };
                    test_s_expr! { *right, $right };
                }
                _ => {
                    println!("ast: {}", $ast);
                    panic!("AST is not a BinOp!");
                }
            }
        };
        // UnOp
        ($ast:expr, ({$op:expr} $right:tt)) => {
            match $ast {
                UnOp { op, right } => {
                    assert_eq!(op.lexeme, $op);
                    test_s_expr! { *right, $right };
                }
                _ => {
                    println!("ast: {}", $ast);
                    panic!("AST is not a UnOp!");
                }
            }
        };
        // Literals and variables
        ($ast:expr, {$literal:expr}) => {
            match $ast {
                Literal(token) => {
                    assert_eq!(token.lexeme, $literal);
                }
                Variable(token) => {
                    assert_eq!(token.lexeme, $literal);
                }
                _ => {
                    println!("ast: {}, expr: {}", $ast, $literal);
                    panic!("AST is not a Literal or Ident!");
                }
            }
        };
    }

    macro_rules! test_parser {
        // If there's only a list of lexemes, just try to parse it!
        ([$($lexeme:expr),+]) => {
            let tokens = vec![$(token($lexeme)),+];
            let mut parser = Parser::new(tokens);
            parser.expression().unwrap();
        };
        // If a second arm is included, we'll try to match the parse tree
        // against the S-expression it contains.
        ([$($lexeme:expr),+], $($s_expr:tt)+) => {
            let tokens = vec![$(token($lexeme)),+];
            let mut parser = Parser::new(tokens);
            let ast = parser.expression().unwrap();
            test_s_expr!(ast, $($s_expr)+);
        };
    }

    ///////////////////////////////////////
    // Terminals: literals and variables //
    ///////////////////////////////////////

    #[test]
    fn single_nat_1() {
        test_parser! {
            [Nat(1)],
            {Nat(1)}
        };
    }

    #[test]
    #[should_panic]
    fn single_nat_2() {
        test_parser! {
            [Nat(0)],
            {Nat(1)}
        };
    }

    #[test]
    fn single_false() {
        test_parser! {
            [False],
            {False}
        }
    }

    #[test]
    fn single_true() {
        test_parser! {
            [True],
            {True}
        }
    }

    #[test]
    fn single_var_1() {
        let name = "foo";
        test_parser! {
            [Ident(name.to_owned())],
            {Ident(name.to_owned())}
        };
    }

    // As a sanity check that the test macros are working, make sure that we
    // don't accept a different identifier.
    #[test]
    #[should_panic]
    fn single_var_2() {
        test_parser! {
            [Ident("foo".to_owned())],
            {Ident("bar".to_owned())}
        };
    }

    ///////////////////////////////////////
    // Unary operators: tildes and bangs //
    ///////////////////////////////////////

    #[test]
    fn tilde_false() {
        test_parser! {
            [Tilde, False],
            ({Tilde} {False})
        }
    }

    #[test]
    fn bang_true() {
        test_parser! {
            [Bang, True],
            ({Bang} {True})
        }
    }

    #[test]
    fn tilde_tilde_false() {
        test_parser! {
            [Tilde, Tilde, False],
            ({Tilde} ({Tilde} {False}))
        }
    }

    #[test]
    fn tilde_bang_false() {
        test_parser! {
            [Tilde, Bang, False],
            ({Tilde} ({Bang} {False}))
        }
    }

    //////////////////////
    // Binary operators //
    //////////////////////

    #[test]
    fn plus_simple() {
        test_parser! {
            [Nat(1), Plus, Nat(1)],
            ({Plus} {Nat(1)} {Nat(1)})
        }
    }

    #[test]
    fn star_simple() {
        test_parser! {
            [Nat(1), Star, Nat(1)],
            ({Star} {Nat(1)} {Nat(1)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn plus_left_assoc() {
        test_parser! {
            [Nat(1), Plus, Nat(2), Plus, Nat(3)],
            ({Plus}
             ({Plus} {Nat(1)} {Nat(2)})
             {Nat(3)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn star_left_assoc() {
        test_parser! {
            [Nat(1), Star, Nat(2), Star, Nat(3)],
            ({Star}
             ({Star} {Nat(1)} {Nat(2)})
             {Nat(3)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn mixed_star_plus() {
        test_parser! {
            [Nat(1), Star, Nat(2), Plus, Nat(3)],
            ({Plus}
             ({Star} {Nat(1)} {Nat(2)})
             {Nat(3)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn mixed_plus_star() {
        test_parser! {
            [Nat(1), Plus, Nat(2), Star, Nat(3)],
            ({Plus} {Nat(1)}
             ({Star} {Nat(2)} {Nat(3)}))
        }
    }

    #[test]
    #[rustfmt::skip]
    fn mixed_plus_equalequal() {
        test_parser! {
            [Nat(2), Plus, Nat(2), EqualEqual, Nat(3), Plus, Nat(1)],
            ({EqualEqual}
             ({Plus} {Nat(2)} {Nat(2)})
             ({Plus} {Nat(3)} {Nat(1)})
            )
        }
    }

    #[test]
    #[should_panic]
    fn plus_nonterminal() {
        test_parser! { [Nat(1), Plus, Plus] }
    }

    //////////////////////////////
    // Binary + unary operators //
    //////////////////////////////

    #[test]
    fn bang_plus() {
        test_parser! {
            [Bang, Nat(1), Plus, Nat(2)],
            ({Plus} ({Bang} {Nat(1)}) {Nat(2)})
        }
    }

    #[test]
    fn plus_bang() {
        test_parser! {
            [Nat(1), Plus, Bang, Nat(2)],
            ({Plus} {Nat(1)} ({Bang} {Nat(2)}))
        }
    }

    #[test]
    fn plus_bang_plus() {
        test_parser! {
            [Nat(1), Plus, Bang, Nat(2), Plus, Nat(3)],
            ({Plus}
             ({Plus} {Nat(1)} ({Bang} {Nat(2)}))
             {Nat(3)})
        }
    }

    ///////////////////////////
    // False-positive checks //
    ///////////////////////////

    // This shouldn't build a tree including the non-operator token `;`
    #[test]
    fn non_operator() {
        test_parser! {
            [Nat(1), Plus, Nat(2), Semicolon, Nat(4)],
            ({Plus} {Nat(1)} {Nat(2)})
        }
    }

    // Repeat the same thing, but with an actual operator, and show that we
    // don't get a false-positive in this case.
    #[test]
    #[should_panic]
    fn non_operator_sanity_check() {
        test_parser! {
            [Nat(1), Plus, Nat(2), Plus, Nat(3), Plus, Nat(4)],
            ({Plus} {Nat(1)}
             ({Plus} {Nat(2)} {Nat(3)}))
        }
    }
}
