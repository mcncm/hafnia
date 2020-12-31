use crate::ast::{self, *};
use crate::cavy_errors::{self, ErrorBuf, Result};
use crate::source::Span;
use crate::token::{
    Lexeme::{self, *},
    Token,
};
use crate::types::Type;
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::vec::IntoIter;

/// The maximum allowed number of arguments to a function
const MAX_ARGS: usize = 64;

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
        m.insert(Minus,      Precedence(2, false));
        m.insert(Star,       Precedence(3, false));
        m.insert(Percent,    Precedence(3, false));
        m.insert(DotDot,     Precedence(4, false));
        m
    };
}

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    errors: ErrorBuf,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: ErrorBuf::new(),
        }
    }

    /// Check the next lexeme
    fn peek_lexeme(&mut self) -> Option<&Lexeme> {
        self.tokens.peek().map(|token| &token.lexeme)
    }

    /// Check for a lexeme and, if it matches, advance.
    fn match_lexeme(&mut self, lexeme: Lexeme) -> bool {
        if let Some(actual) = self.tokens.peek() {
            if actual.lexeme == lexeme {
                self.forward();
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    fn forward(&mut self) {
        self.tokens.next();
    }

    /// Consumes the parser, generating a list of statements
    pub fn parse(mut self) -> std::result::Result<Vec<Stmt>, ErrorBuf> {
        let mut stmts = vec![];
        loop {
            match self.declaration() {
                Ok(Some(stmt)) => stmts.push(stmt),
                Err(err) => self.errors.push(err),
                Ok(None) => {
                    break;
                }
            }
        }

        if self.errors.is_empty() {
            Ok(stmts)
        } else {
            Err(self.errors)
        }
    }

    fn consume(&mut self, lexeme: Lexeme) -> Result<Token> {
        let token = self.tokens.next().ok_or(errors::UnexpectedEof {
            // FIXME this default is flagrantly incorrect
            span: Span::default(),
        })?;
        if token.lexeme == lexeme {
            return Ok(token);
        }
        Err(Box::new(errors::ExpectedToken {
            span: token.span,
            expected: lexeme,
            actual: token.lexeme,
        }))
    }

    /// Because identifiers have a parameter, we can’t use the regular `consume`
    /// method with them. Alternatively, we could use a macro, but this adds unnecessary complexity.
    fn consume_ident(&mut self) -> Result<String> {
        // TODO This unwrap isn’t safe; you could be at EOF
        let token = self.tokens.next().ok_or(errors::UnexpectedEof {
            // FIXME This span is blatantly wrong
            span: Span::default(),
        })?;
        match token.lexeme {
            Lexeme::Ident(name) => Ok(name),
            lexeme => Err(Box::new(errors::ExpectedIdentifier {
                span: token.span,
                actual: lexeme,
            })),
        }
    }

    /// A declaration, which is either a definition or a statement
    pub fn declaration(&mut self) -> Result<Option<Stmt>> {
        if self.peek_lexeme() == None {
            return Ok(None);
        }

        // TODO Check for assignment (currently in `self.statement`)
        if self.match_lexeme(Lexeme::Fn) {
            let def = self.function_definition()?;
            let stmt = StmtKind::Item(def).into();
            Ok(Some(stmt))
        } else {
            Ok(Some(self.statement()?))
        }
    }

    /// Produces a statement
    pub fn statement(&mut self) -> Result<Stmt> {
        match self.peek_lexeme() {
            Some(Print) => Ok(self.print_stmt()?),
            Some(Let) => Ok(self.local()?),
            // Must be an expression next!
            Some(_) => {
                let expr = Box::new(self.expression()?);
                if expr.kind.requires_semicolon() & self.match_lexeme(Semicolon) {
                    Ok(StmtKind::ExprSemi(expr).into())
                } else {
                    Ok(StmtKind::Expr(expr).into())
                }
            }
            // You should always have another token available because this is
            // called from within `declaration`.
            None => unreachable!(),
        }
    }

    fn function_definition(&mut self) -> Result<Item> {
        let name = self.consume_ident()?;
        self.consume(Lexeme::LParen)?;
        let params = self.finish_function_params()?;
        let typ = self.function_return_type()?;
        self.consume(Lexeme::LBrace)?;
        let body = Box::new(self.block()?);
        let kind = ItemKind::Fn {
            name,
            params,
            typ,
            body,
            docstring: None,
        };
        Ok(Item {
            kind,
            span: Span::default(),
        })
    }

    fn finish_function_params(&mut self) -> Result<Vec<(String, Annot)>> {
        if self.match_lexeme(RParen) {
            return Ok(vec![]);
        }

        let mut params = vec![self.function_param()?];
        while self.match_lexeme(Comma) {
            params.push(self.function_param()?);
        }
        self.consume(RParen)?;

        Ok(params)
    }

    fn function_param(&mut self) -> Result<(String, Annot)> {
        let name = self.consume_ident()?;
        self.consume(Colon)?;
        let ty = self.type_annotation()?;
        Ok((name, ty))
    }

    fn function_return_type(&mut self) -> Result<Option<Annot>> {
        if self.match_lexeme(MinusRAngle) {
            return Ok(Some(self.type_annotation()?));
        }
        Ok(None)
    }

    /// Returns either an assignment statement, as in:
    /// ```cavy
    /// let x = 3;
    /// ```
    /// or a let-expression, as in:
    /// ```cavy
    /// let y = 3;
    /// let x = y in {
    ///     x + 1
    /// }
    /// ```
    fn local(&mut self) -> Result<Stmt> {
        self.forward();
        let lhs = Box::new(self.lvalue()?);
        let ty = if self.match_lexeme(Colon) {
            Some(self.type_annotation()?)
        } else {
            None
        };
        self.consume(Lexeme::Equal)?;
        let rhs = Box::new(self.expression()?);
        // But this could still be a *let expression statement*. We have to check
        // for this case.
        if self.match_lexeme(Lexeme::In) {
            self.consume(Lexeme::LBrace)?;
            let body = Box::new(self.block()?);
            let expr_kind = ExprKind::Let { lhs, rhs, body };
            Ok(StmtKind::Expr(Box::new(expr_kind.into())).into())
        } else {
            self.consume(Lexeme::Semicolon)?;
            Ok(StmtKind::Local { lhs, rhs, ty }.into())
        }
    }

    /// Recursively build an LValue
    fn lvalue(&mut self) -> Result<LValue> {
        // TODO should check that all names are unique
        match self.peek_lexeme() {
            Some(Lexeme::Ident(_)) => {
                let token = self.tokens.next().unwrap();
                let ident = ast::Ident::try_from(token).unwrap();
                Ok(LValueKind::Ident(ident).into())
            }
            Some(LParen) => {
                self.forward();
                self.finish_lvalue_tuple()
            }
            _ => todo!(),
        }
    }

    /// Having already encoundered an open-paren, finish building the lvalue.
    /// This algorithm is consistent with that for tuple expressions: nonempty
    /// tuple patterns may have a trailing comma if they contain more than one
    /// element; they must have a trailing comma if they have exactly one
    /// element. This is the same as Rust.
    ///
    /// NOTE We should inline this because it’s only called from `lvalue`, with which
    /// it is mutually recursive.
    #[inline(always)]
    fn finish_lvalue_tuple(&mut self) -> Result<LValue> {
        if self.match_lexeme(Lexeme::RParen) {
            return Ok(LValueKind::Tuple(vec![]).into());
        }

        let head = self.lvalue()?;
        let lvalue = if let Some(&Comma) = self.peek_lexeme() {
            // Tuples with one element should have a single trailing comma to
            // disambiguate from groups.
            let mut items = vec![head];
            while self.match_lexeme(Comma) {
                if let Some(&RParen) = &self.peek_lexeme() {
                    break;
                }
                items.push(self.lvalue()?);
            }
            LValueKind::Tuple(items).into()
        } else {
            // If there were no commas, we should just regard this as a pair of
            // grouping parentheses.
            head
        };
        self.consume(RParen)?;
        Ok(lvalue)
    }

    fn print_stmt(&mut self) -> Result<Stmt> {
        self.forward();
        let expr = self.expression()?;
        self.consume(Lexeme::Semicolon)?;
        Ok(StmtKind::Print(Box::new(expr)).into())
    }

    fn if_expr(&mut self) -> Result<Expr> {
        self.forward();
        // Here we assume that
        let cond = Box::new(self.expression()?);
        self.consume(Lexeme::LBrace)?;
        let then_branch = Box::new(self.block()?);

        let mut else_branch = None;
        if self.match_lexeme(Lexeme::Else) {
            self.consume(Lexeme::LBrace)?;
            else_branch = Some(Box::new(self.block()?));
        }
        let kind = ExprKind::If {
            cond,
            then_branch,
            else_branch,
        };
        Ok(kind.into())
    }

    fn for_expr(&mut self) -> Result<Expr> {
        self.forward();
        let bind = Box::new(self.lvalue()?);
        self.consume(Lexeme::In)?;
        let iter = Box::new(self.expression()?);
        self.consume(Lexeme::LBrace)?;
        let body = Box::new(self.block()?);
        let kind = ExprKind::For { bind, iter, body };
        Ok(kind.into())
    }

    fn block_expr(&mut self) -> Result<Expr> {
        Ok(ExprKind::Block(self.block()?).into())
    }

    fn block(&mut self) -> Result<Block> {
        let mut stmts: Vec<Stmt> = vec![];
        while let Some(lexeme) = self.peek_lexeme() {
            if lexeme == &Lexeme::RBrace {
                break;
            }
            stmts.push(self.statement()?);
        }
        self.consume(Lexeme::RBrace)?;
        Ok(Block { stmts })
    }

    fn expr_stmt(&mut self) -> Result<Stmt> {
        let res = StmtKind::Expr(Box::new(self.expression()?));
        self.consume(Lexeme::Semicolon)?;
        Ok(res.into())
    }

    pub fn expression(&mut self) -> Result<Expr> {
        match self.peek_lexeme() {
            Some(Lexeme::If) => self.if_expr(),
            Some(Lexeme::For) => self.for_expr(),
            Some(Lexeme::LBrace) => self.block_expr(),
            Some(_) => {
                let lhs = self.unary()?;
                self.precedence_climb(lhs, 0)
            }
            _ => unreachable!(),
        }
    }

    fn unary(&mut self) -> Result<Expr> {
        if let Some(Bang) | Some(Tilde) | Some(Question) = self.peek_lexeme() {
            let op = self.tokens.next().unwrap();
            let right = self.unary()?;
            let kind = ExprKind::UnOp {
                op,
                right: Box::new(right),
            };
            return Ok(kind.into());
        } else if self.match_lexeme(LBracket) {
            return self.finish_array();
        }
        self.call()
    }

    fn finish_array(&mut self) -> Result<Expr> {
        // Empty array:
        if self.match_lexeme(RBracket) {
            return Ok(ExprKind::ExtArr(vec![]).into());
        }

        // Otherwise, there is at least one item:
        let item = self.expression()?;
        let arr = if self.match_lexeme(Semicolon) {
            let item = Box::new(item);
            let reps = Box::new(self.expression()?);
            ExprKind::IntArr { item, reps }
        } else {
            let mut items = vec![item];
            loop {
                if !self.match_lexeme(Comma) {
                    break;
                }
                items.push(self.expression()?);
            }
            ExprKind::ExtArr(items)
        };
        self.consume(RBracket)?;
        Ok(arr.into())
    }

    fn type_annotation(&mut self) -> Result<Annot> {
        // Get another token. We're anticipating being able to form a type
        // annotation here, so it's an error if none is available.
        let Token { lexeme, span } = self.tokens.next().ok_or(errors::UnexpectedEof {
            // FIXME this default is flagrantly incorrect
            span: Span::default(),
        })?;

        // TODO How to make this more succinct: a macro? It doesn't seem
        // possible for macros to expand to match arms. An or-pattern? Not
        // stable yet.
        let ty = match lexeme {
            Bool => Annot {
                span,
                kind: AnnotKind::Bool,
            },
            U8 => Annot {
                span,
                kind: AnnotKind::U8,
            },
            U16 => Annot {
                span,
                kind: AnnotKind::U16,
            },
            U32 => Annot {
                span,
                kind: AnnotKind::U32,
            },
            LBracket => self.finish_array_type(span)?,
            LParen => self.finish_tuple_type(span)?,
            Question => {
                let ty_inner = self.type_annotation()?;
                Annot {
                    span: span.join(&ty_inner.span).unwrap(),
                    kind: AnnotKind::Question(Box::new(ty_inner)),
                }
            }
            _ => todo!(),
        };

        Ok(ty)
    }

    /// Finish parsing an array type.
    fn finish_array_type(&mut self, opening: Span) -> Result<Annot> {
        let ty = Box::new(self.type_annotation()?);
        let closing = self.consume(RBracket)?;
        let span = opening.join(&closing.span).unwrap();
        Ok(Annot {
            span,
            kind: AnnotKind::Array(ty),
        })
    }

    /// Finish parsing a type that may be either a tuple or the unit type.
    fn finish_tuple_type(&mut self, opening: Span) -> Result<Annot> {
        let mut types = vec![];
        while !self.match_lexeme(RParen) {
            types.push(self.type_annotation()?);
            self.consume(Comma)?;
        }
        let closing = self.consume(RParen)?;
        let span = opening.join(&closing.span).unwrap();
        let kind = if types.is_empty() {
            AnnotKind::Unit
        } else {
            AnnotKind::Tuple(types)
        };
        Ok(Annot { span, kind })
    }

    /// Call a function or index into an array.
    #[rustfmt::skip]
    fn call(&mut self) -> Result<Expr> {
        let mut expr = self.primary()?;

        // This is a function call
        if self.match_lexeme(LParen) {
            if let ExprKind::Ident(ident @ ast::Ident { .. }) = expr.kind {
                return self.finish_call(ident);
            } else {
                return Ok(expr);
            }
        }

        // Otherwise, this is either a bunch of nested index operations, or it's
        // just a primary token. Build up indexing operations as long as there
        // are open-brackets to consume.
        while self.match_lexeme(Lexeme::LBracket) {
            expr = self.finish_index(expr)?;
        }

        Ok(expr)
    }

    // Inline(always) because there is only one call site.
    #[inline(always)]
    fn finish_call(&mut self, callee: ast::Ident) -> Result<Expr> {
        let mut args = vec![];
        if self.peek_lexeme() != Some(&RParen) {
            loop {
                args.push(self.expression()?);
                if !self.match_lexeme(Comma) {
                    break;
                }
            }
        }
        let paren = self.consume(RParen)?;
        let kind = ExprKind::Call {
            callee,
            args,
            paren,
        };
        Ok(kind.into())
    }

    #[inline(always)]
    fn finish_index(&mut self, head: Expr) -> Result<Expr> {
        let head = Box::new(head);
        let index = Box::new(self.expression()?);
        let bracket = self.consume(RBracket)?;
        let kind = ExprKind::Index {
            head,
            index,
            bracket,
        };
        Ok(kind.into())
    }

    fn primary(&mut self) -> Result<Expr> {
        let token = self.tokens.next().unwrap();
        match token.lexeme {
            Nat(_) | True | False => {
                let kind = ExprKind::Literal(token);
                Ok(kind.into())
            }
            Ident(_) => {
                let ident = ast::Ident::try_from(token).unwrap();
                let kind = ExprKind::Ident(ident);
                Ok(kind.into())
            }
            LParen => self.finish_group(),

            lexeme => Err(Box::new(errors::ExpectedPrimaryToken {
                // Guaranteed not to be EOF!
                span: token.span,
                actual: lexeme,
            })),
        }
    }

    /// After reaching an `(` in the position of a primary token, we must have
    /// either a group or a sequence.
    fn finish_group(&mut self) -> Result<Expr> {
        // `()` shall be an empty sequence, and evaluate to an empty tuple.
        if self.match_lexeme(Lexeme::RParen) {
            return Ok(ExprKind::Tuple(vec![]).into());
        }

        let head = self.expression()?;
        let expr = if let Some(&Lexeme::Comma) = self.peek_lexeme() {
            // Tuples with one element should have a single trailing comma to
            // disambiguate from groups.
            let mut items = vec![head];
            while self.match_lexeme(Lexeme::Comma) {
                if let Some(&Lexeme::RParen) = &self.peek_lexeme() {
                    break;
                }
                items.push(self.expression()?);
            }
            ExprKind::Tuple(items).into()
        } else {
            // If there were no commas, we should have a single expression
            // followed by a close-paren, and return a group.
            head
        };
        self.consume(RParen)?;
        Ok(expr)
    }

    fn precedence_climb(&mut self, lhs: Expr, min_precedence: u8) -> Result<Expr> {
        let mut lhs = lhs.kind;
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
                lhs = ExprKind::BinOp {
                    op: outer,
                    left: Box::new(lhs.into()),
                    right: Box::new(rhs),
                };
            } else {
                break;
            }
        }
        Ok(lhs.into())
    }

    fn synchronize(&mut self, _err: &str) {
        todo!();
    }
}

mod errors {
    use crate::cavy_errors::Diagnostic;
    use crate::source::Span;
    use cavy_macros::Diagnostic;
    // This will become redundant when diagnostics only implement `Diagnostic`
    use super::Lexeme;
    use std::error::Error;

    #[derive(Diagnostic)]
    pub struct ExpectedToken {
        #[msg = "expected `{expected}`, found `{actual}`"]
        pub span: Span,
        /// The expected lexeme
        pub expected: Lexeme,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    pub struct ExpectedIdentifier {
        #[msg = "expected identifier, found `{actual}`"]
        pub span: Span,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    pub struct UnexpectedEof {
        #[msg = "unexpected end of file"]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    pub struct ExpectedPrimaryToken {
        #[msg = "expected primary token, found `{actual}`"]
        pub span: Span,
        /// The lexeme actually found
        pub actual: Lexeme,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ExprKind::{self, *};
    use crate::token::Token;
    use Lexeme::*;

    //////////////////////////////////////////////////////
    // Functions and macros for constructing test cases //
    //////////////////////////////////////////////////////

    fn token(lexeme: Lexeme) -> Token {
        Token {
            lexeme,
            span: Span::default(),
        }
    }

    /// We'll use this macro to test the parser. The parse tree templates will
    /// take the form of S-expressions. Two avoid wrangling with the Rust macro
    /// system more than necessary, the leaves of the S-expressions must be
    /// enclosed in curly braces.
    macro_rules! test_s_expr {
        // BinOp
        ($ast:expr, ({$op:expr} $left:tt $right:tt)) => {
            match &$ast.kind {
                BinOp { op, left, right } => {
                    assert_eq!(op.lexeme, $op);
                    test_s_expr! { *left, $left };
                    test_s_expr! { *right, $right };
                }
                _ => {
                    panic!("AST is not a BinOp!");
                }
            }
        };
        // UnOp
        ($ast:expr, ({$op:expr} $right:tt)) => {
            match &$ast.kind {
                UnOp { op, right } => {
                    assert_eq!(op.lexeme, $op);
                    test_s_expr! { *right, $right };
                }
                _ => {
                    panic!("AST is not a UnOp!");
                }
            }
        };
        // Literals and variables
        ($ast:expr, {$literal:expr}) => {
            match &$ast.kind {
                Literal(token) => {
                    assert_eq!(token.lexeme, $literal);
                }
                ExprKind::Ident(ident) => {
                    // For backwards compatibility of this test: convert the Ident back into a Lexeme::Ident.
                    let lexeme = Lexeme::Ident(ident.name.clone());
                    assert_eq!(lexeme, $literal);
                }
                _ => {
                    panic!("AST is not a Literal or Ident!");
                }
            }
        };
    }

    /// This macro compares puts a list of lexemes into a parser and compares
    /// the output to a literal syntax tree.
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
            [Lexeme::Ident(name.to_owned())],
            {Lexeme::Ident(name.to_owned())}
        };
    }

    // As a sanity check that the test macros are working, make sure that we
    // don't accept a different identifier.
    #[test]
    #[should_panic]
    fn single_var_2() {
        test_parser! {
            [Lexeme::Ident("foo".to_owned())],
            {Lexeme::Ident("bar".to_owned())}
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
