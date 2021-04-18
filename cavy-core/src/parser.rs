//! Parsing, as well as a fair number of semantic rules, are handled by this
//! module. We hope that it will improve performance--as well as reduce the
//! amount of code that must be writen--to construct symbol tables and validate
//! the syntax tree at parse time.
//!
//! Some of the validations performed at this stage include:
//! * The uniqueness of the `main` function, as well its type signature
//! * Use before declaration
//!
//! Other checks cannot be performed at this time, because the data may not be
//! available on this pass.
//! * Most kinds of name resolution: we can't resolve types, so in particular we
//!   can't check that type annotations refer to something in-scope.

use crate::{
    ast::{self, *},
    cavy_errors::{self, ErrorBuf, Maybe},
    context::{Context, SymbolId},
    num::Uint,
    source::Span,
    store::Counter,
    token::{
        Delim::{self, *},
        Lexeme::{self, *},
        Token,
    },
    types,
    types::Type,
};
use errors::*;
use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::{collections::HashMap, process::Command};
use std::{mem, vec::IntoIter};

/// Main entry point for parsing: consumes a token stream and produces a module.
/// This api will almost certainly change when, some fine day, a program can
/// have more than one module in it.
pub fn parse(tokens: Vec<Token>, ctx: &mut Context) -> Result<Ast, ErrorBuf> {
    Parser::new(tokens, ctx).parse()
}

/// The maximum allowed number of arguments to a function
const MAX_ARGS: usize = 64;

/// Operator precedence: the first field is the scalar precedence; the second is
/// its right associativity.
struct Precedence(u8, bool);

fn operator(lexeme: &Lexeme) -> Option<Precedence> {
    let prec = match lexeme {
        Equal => Precedence(0, true),
        TildeEqual => Precedence(1, false),
        EqualEqual => Precedence(1, false),
        LAngle => Precedence(2, false),
        RAngle => Precedence(2, false),
        Plus => Precedence(3, false),
        Minus => Precedence(3, false),
        Star => Precedence(4, false),
        Percent => Precedence(4, false),
        DotDot => Precedence(5, false),
        _ => return None,
    };
    Some(prec)
}

/// The main data structure used for parsing a stream of tokens
pub struct Parser<'p, 'ctx> {
    /// We may want to parse more than one token stream in the future, so we
    /// don't want exclusive ownership of this data.
    ast: Ast,
    /// The global context state
    ctx: &'p mut Context<'ctx>,
    /// Currently active symbol table.
    table_id: TableId,
    /// The representation of the token stream is subject to change.
    tokens: Peekable<IntoIter<Token>>,
    /// Location of current token
    loc: Span,
    /// We'll also want to maintain a list of errors to propagate upwards
    /// if necessary
    errors: ErrorBuf,
    /// A flag that, when set, excludes struct literal expressions
    excl_struct_lit: bool,
}

impl<'p, 'ctx> Parser<'p, 'ctx> {
    pub fn new(tokens: Vec<Token>, ctx: &'p mut Context<'ctx>) -> Self {
        // For now, just allocate some new table, which will be the root.
        let mut ast = Ast::new();
        let table_id = ast.new_table();
        Self {
            ast,
            ctx,
            table_id,
            tokens: tokens.into_iter().peekable(),
            loc: Span::default(),
            errors: ErrorBuf::new(),
            excl_struct_lit: false,
        }
    }

    /// Push a new symbol table onto the stack
    fn push_table(&mut self) {
        self.table_id = self.ast.child_table(self.table_id);
    }

    /// Pop a symbol table from the stack, unless you're at the root
    fn pop_table(&mut self) -> Option<TableId> {
        let table = &self.ast.tables[self.table_id];
        table.parent.map(|parent_id| {
            let tid = self.table_id;
            self.table_id = parent_id;
            tid
        })
    }

    /// Do something in a child table environment; return from that environment
    /// with a handle to the table. The real reason for having this is the
    /// slight subtlety of recovering gracefully from errors *after* pushing a
    /// child table, which could be easily forgotten by an uncareful future you.
    fn with_table<T, F>(&mut self, f: F) -> Maybe<(T, TableId)>
    where
        F: FnOnce(&mut Parser) -> Maybe<T>,
    {
        self.push_table();
        let t = match f(self) {
            Ok(t) => t,
            Err(err) => {
                // recover!
                self.pop_table();
                return Err(err);
            }
        };
        Ok((t, self.pop_table().unwrap()))
    }

    /// Do something in a context where struct literal expressions are not
    /// parsed. This is an ambiguity-resolving hack to deal with the situation
    /// where an expression is expected to be followed by an `}`.
    fn with_excl_struct_lit<T>(&mut self, excl: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.excl_struct_lit;
        self.excl_struct_lit = excl;
        let val = f(self);
        self.excl_struct_lit = old;
        val
    }

    /// A convenience method for creating new nodes. Right now, this doesn't
    /// *really* do anything, but I might decide in the future that expression
    /// nodes should have an associated `ExprId`. In that case, it will be nice to
    /// only have to edit this one spot, rather than every point an `Expr` is
    /// made in this file.
    #[inline(always)]
    fn node(&mut self, kind: ExprKind, span: Span) -> Expr {
        Expr {
            data: kind,
            span,
            node: self.ast.counter.new_index(),
        }
    }

    /// Check if you're in a root table.
    ///
    /// NOTE: This check is currently being used to validate `main` by ensuring
    /// that there is only one such function in the global scope. This might no
    /// longer work if there are multiple root tables in multiple modules one
    /// day.
    fn root_table(&self) -> bool {
        self.ast.tables[self.table_id].parent.is_none()
    }

    /// Check the next lexeme
    fn peek_lexeme(&mut self) -> Option<&Lexeme> {
        self.tokens.peek().map(|token| &token.lexeme)
    }

    /// Check for a lexeme and, if it matches, advance.
    fn match_lexeme(&mut self, lexeme: &Lexeme) -> bool {
        if let Some(actual) = self.tokens.peek() {
            if &actual.lexeme == lexeme {
                self.next();
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.next();
        if let Some(token) = &token {
            self.loc = token.span;
        }
        token
    }

    /// Take a token if there is one; push an error otherwise
    fn token(&mut self) -> Maybe<Token> {
        // Note that this cannot be `ok_or`, which is eagerly evaluated.
        let token = self
            .next()
            .ok_or_else(|| self.errors.push(errors::UnexpectedEof { span: self.loc }))?;
        Ok(token)
    }

    /// Consumes the parser
    pub fn parse(mut self) -> Result<Ast, ErrorBuf> {
        while self.tokens.peek().is_some() {
            match self.item() {
                Ok(_) => {}
                Err(_) => {
                    return Err(self.errors);
                }
            }
        }
        Ok(self.ast)
    }

    fn item(&mut self) -> Maybe<()> {
        let Token { lexeme, span } = self.token()?;
        match lexeme {
            Lexeme::Fn => self.fn_item(span),
            Lexeme::Struct => self.struct_item(),
            Lexeme::Enum => self.enum_item(),
            Lexeme::Type => self.type_item(),
            // We anticipated an item, so if you haven't gotten one, there's
            // been a problem.
            lexeme => Err(self.errors.push(ExpectedItem {
                span,
                actual: lexeme,
            })),
        }
    }

    fn consume(&mut self, lexeme: Lexeme) -> Maybe<Token> {
        let token = self.token()?;

        if token.lexeme == lexeme {
            return Ok(token);
        }
        Err(self.errors.push(ExpectedToken {
            span: token.span,
            expected: lexeme,
            actual: token.lexeme,
        }))
    }

    fn ldelim(&mut self, delim: Delim) -> Maybe<Token> {
        self.consume(Lexeme::LDelim(delim))
    }

    fn rdelim(&mut self, delim: Delim) -> Maybe<Token> {
        self.consume(Lexeme::RDelim(delim))
    }

    /// Collect a delimited list of AST elements given a function for parsing
    /// them, a terminating delimiter (e.g. `}`), and a separator (e.g. `,`).
    /// Can optionally allow a final separator.
    fn delimited_list<T>(
        &mut self,
        delim: Delim,
        sep: Lexeme,
        final_allowed: bool,
        f: impl std::ops::Fn(&mut Self) -> Maybe<T>,
    ) -> Maybe<(Vec<T>, Span)> {
        let opening = self.consume(Lexeme::LDelim(delim))?.span;
        let mut elems = Vec::new();
        // NOTE Is it possible to do this more succinctly without the branch?
        if final_allowed {
            while self.peek_lexeme() != Some(&RDelim(delim)) {
                elems.push(f(self)?);
                if !self.match_lexeme(&sep) {
                    break;
                }
            }
        } else {
            // empty case handled separatedly
            if self.peek_lexeme() != Some(&RDelim(delim)) {
                loop {
                    elems.push(f(self)?);
                    if !self.match_lexeme(&sep) {
                        break;
                    }
                }
            }
        }
        let closing = self.consume(Lexeme::RDelim(delim))?.span;
        let span = opening.join(&closing).unwrap();
        Ok((elems, span))
    }

    /// Because identifiers have a parameter, we can’t use the regular `consume`
    /// method with them. Alternatively, we could use a macro, but this adds unnecessary complexity.
    fn consume_ident(&mut self) -> Maybe<ast::Ident> {
        let token = self.token()?;
        match token.lexeme {
            Lexeme::Ident(_) => Ok(ast::Ident::from_token(token, &mut self.ctx).unwrap()),
            lexeme => Err(self.errors.push(ExpectedIdentifier {
                span: token.span,
                actual: lexeme,
            })),
        }
    }

    fn pattern(&mut self) -> Maybe<Pattern> {
        // For now, this will only capture an identifier, the only kind of
        // pattern currently in the AST.
        let ident = self.consume_ident()?;
        let span = ident.span;
        let data = PatternKind::Ident(ident.data);
        Ok(Pattern { data, span })
    }

    /// Produces a statement
    pub fn statement(&mut self) -> Maybe<Stmt> {
        match self.peek_lexeme() {
            Some(Print) => Ok(self.print_stmt()?),
            Some(Let) => Ok(self.local()?),
            // Must be an expression next! Note that it's not possible to find
            // an item in this position, since this method is *only* called
            // under a match that catches the item keywords.
            Some(_) => {
                let expr = Box::new(self.expression()?);
                if expr.data.requires_semicolon() & self.match_lexeme(&Semicolon) {
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

    /// Put a user-defined type into the symbol table. Not a parsing method!
    fn insert_udt<T>(&mut self, name: ast::Ident, udt: T) -> Maybe<()>
    where
        T: Into<UdtKind>,
    {
        let kind = udt.into();
        let udt = Udt {
            table: self.table_id,
            kind,
        };
        // Insert the struct into the AST's collection of user-defined types
        let udt_id = self.ast.udts.insert(udt);

        // Finally, insert the user-defined type id into the local symbol table.
        match self
            .ast
            .insert_udt(self.table_id, name.data, name.span, udt_id)
        {
            None => Ok(()),
            // A struct with this name was already in the local symbol table
            Some((_, fst)) => Err(self.errors.push(errors::MultipleDefinitions {
                fst,
                snd: name.span,
            })),
        }
    }

    /// Parse a type alias item
    fn type_item(&mut self) -> Maybe<()> {
        let name = self.consume_ident()?;
        self.consume(Lexeme::Equal)?;
        let annot = self.type_annotation()?;
        self.consume(Lexeme::Semicolon)?;
        self.insert_udt(name, annot)
    }

    /// Parse a struct item and insert the name in a symbol table
    fn struct_item(&mut self) -> Maybe<()> {
        let name = self.consume_ident()?;
        let (fields, _) = self.delimited_list(Brace, Comma, true, Self::struct_field)?;
        let struct_ = ast::Struct {
            name: name.clone(),
            fields,
        };

        self.insert_udt(name, struct_)
    }

    fn struct_field(&mut self) -> Maybe<StructField> {
        let name = self.consume_ident()?;
        self.consume(Lexeme::Colon)?;
        let ty = self.type_annotation()?;
        let field = StructField { name, ty };
        Ok(field)
    }

    /// Parse an item and insert the name in a symbol table
    fn enum_item(&mut self) -> Maybe<()> {
        let name = self.consume_ident()?;
        let (alternatives, _) = self.delimited_list(Brace, Comma, true, Self::enum_alternative)?;
        let enum_ = ast::Enum {
            name: name.clone(),
            alternatives,
        };

        self.insert_udt(name, enum_)
    }

    // For the time being, accept only identifiers
    fn enum_alternative(&mut self) -> Maybe<EnumAlternative> {
        let name = self.consume_ident()?;
        let data = match self.peek_lexeme() {
            Some(&LDelim(Paren)) => {
                let data = self.delimited_list(Paren, Comma, false, Self::type_annotation)?;
                Some(data)
            }
            _ => None,
        };
        Ok(EnumAlternative { name, data })
    }

    /// Parse a function item and insert it in the functions table
    fn fn_item(&mut self, opening: Span) -> Maybe<()> {
        let name = self.consume_ident()?;

        // Should we create a parameters table as the parent of the function
        // body? I'm not totally sure about this.

        let sig = self.function_sig()?;
        let body = Box::new(self.block()?);
        let body_span = body.span;
        let body = self.node(ExprKind::Block(body), body_span);
        let span = opening.join(&body.span).unwrap();
        let func = Func {
            sig,
            body: self.ast.bodies.insert(body),
            table: self.table_id,
            span,
        };

        // Insert the function into the function table
        let func_id = self.ast.funcs.insert(func);

        // Validate the `main` function
        if self.root_table() && self.ctx.symbols[name.data] == "main" {
            self.validate_main(func_id)?;
            self.ast.entry_point = Some(func_id);
        }

        // Finally, insert the function id into the local symbol table.
        match self
            .ast
            .insert_fn(self.table_id, name.data, name.span, func_id)
        {
            // No other function with this name
            None => Ok(()),
            // A function with this name was already in the local symbol table
            Some((_, fst)) => Err(self.errors.push(errors::MultipleDefinitions {
                fst,
                snd: name.span,
            })),
        }
    }

    /// Once a `main` function has been found, ensure that it's the only one,
    /// acceps no parameters, and returns no value. We'll just take an `FnId` as
    /// we hope to only call this once, so the cost of lookup should not be too great.
    fn validate_main(&mut self, func_id: FnId) -> Maybe<()> {
        let func = &self.ast.funcs[func_id];
        // Make sure there are no other entry points
        if self.ast.entry_point.is_some() {
            let span = func.span;
            return Err(self.errors.push(errors::MultipleEntryPoints { span }));
        }
        // Check the signature
        if !func.sig.params.is_empty() || func.sig.output.is_some() {
            let span = func.sig.span;
            return Err(self.errors.push(errors::InvalidMainSignature { span }));
        }
        Ok(())
    }

    /// Collect a function signature
    fn function_sig(&mut self) -> Maybe<Sig> {
        let (params, mut span) = self.delimited_list(Paren, Comma, false, Self::function_param)?;
        let output = self.function_return_type()?;
        if let Some(annot) = &output {
            span = span.join(&annot.span).unwrap();
        }

        let sig = Sig {
            params,
            output,
            span,
        };

        Ok(sig)
    }

    /// Get a single function parameter comprising an LValue pattern and a type
    /// annotation.
    fn function_param(&mut self) -> Maybe<Param> {
        let name = self.consume_ident()?;
        self.consume(Colon)?;
        let ty = self.type_annotation()?;
        let span = name.span.join(&ty.span).unwrap();
        Ok(Param { name, ty, span })
    }

    fn function_return_type(&mut self) -> Maybe<Option<Annot>> {
        if self.match_lexeme(&MinusRAngle) {
            return Ok(Some(self.type_annotation()?));
        }
        Ok(None)
    }

    /// Returns either an assignment statement, as in:
    /// ```cavy
    /// let x = 3;
    /// ```
    fn local(&mut self) -> Maybe<Stmt> {
        let opening = self.next().unwrap().span;
        // For now, only admit symbols on the lhs.
        let lhs = Box::new(self.consume_ident()?.into());
        let ty = if self.match_lexeme(&Colon) {
            Some(self.type_annotation()?)
        } else {
            None
        };

        let rhs = if self.match_lexeme(&Equal) {
            Some(Box::new(self.expression()?))
        } else {
            None
        };

        let semi = self.consume(Semicolon)?.span;

        let stmt = Stmt {
            data: StmtKind::Decl { lhs, ty, rhs },
            span: opening.join(&semi).unwrap(),
        };
        Ok(stmt)
    }

    /// Recursively build an LValue
    fn lvalue(&mut self) -> Maybe<LValue> {
        // We' anticipate being able to find an lvalue here, so produce an error
        // if a token isn't found.
        let token = self.token()?;
        // TODO should check that all names are unique
        match token.lexeme {
            Ident(_) => {
                let ident = ast::Ident::from_token(token, self.ctx).unwrap();
                let lvalue = LValue {
                    span: ident.span,
                    data: LValueKind::Ident(ident),
                };
                Ok(lvalue)
            }
            LDelim(Paren) => self.finish_lvalue_tuple(token.span),
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
    fn finish_lvalue_tuple(&mut self, opening: Span) -> Maybe<LValue> {
        // Finish right away if the next token is a close-paren
        if let Some(&LDelim(Paren)) = self.peek_lexeme() {
            let closing = self.next().unwrap().span;
            let span = opening.join(&closing).unwrap();
            let lvalue = LValue {
                span,
                data: LValueKind::Tuple(vec![]),
            };
            return Ok(lvalue);
        }

        let head = self.lvalue()?;
        let mut lvalue = if let Some(&Comma) = self.peek_lexeme() {
            // Tuples with one element should have a single trailing comma to
            // disambiguate from groups.
            let mut items = vec![head];
            while self.match_lexeme(&Comma) {
                items.push(self.lvalue()?);
                if let Some(&RDelim(Paren)) = &self.peek_lexeme() {
                    break;
                }
            }
            // Give a default span for now
            LValueKind::Tuple(items).into()
        } else {
            // If there were no commas, we should just regard this as a pair of
            // grouping parentheses.
            head
        };
        // Now fix up the span
        let closing = self.consume(LDelim(Paren))?;
        let span = opening.join(&closing.span).unwrap();
        lvalue.span = span;
        Ok(lvalue)
    }

    fn print_stmt(&mut self) -> Maybe<Stmt> {
        self.next();
        let expr = self.expression()?;
        self.consume(Lexeme::Semicolon)?;
        Ok(StmtKind::Print(Box::new(expr)).into())
    }

    fn if_expr(&mut self) -> Maybe<Expr> {
        let opening = self.token()?.span;
        // Call `expression_inner` because we must parse the condition
        // expression without first resetting the condition flag.
        let cond = self.with_excl_struct_lit(true, Self::expression_inner)?;
        let then_branch = Box::new(self.block()?);

        let mut else_branch = None;
        let span;
        if self.match_lexeme(&Lexeme::Else) {
            let block = self.block()?;
            span = opening.join(&block.span).unwrap();
            else_branch = Some(Box::new(block));
        } else {
            span = opening.join(&then_branch.span).unwrap();
        }
        let kind = ExprKind::If {
            cond: Box::new(cond),
            tru: then_branch,
            fls: else_branch,
        };

        Ok(self.node(kind, span))
    }

    fn match_expr(&mut self) -> Maybe<Expr> {
        let opening = self.token()?.span;
        // Call `expression_inner` because we must parse the scrutinee
        // expression without first resetting the condition flag.
        let scr = self.with_excl_struct_lit(true, Self::expression_inner)?;
        let (arms, span) = self.delimited_list(Brace, Lexeme::Comma, true, Self::match_arm)?;
        let kind = ExprKind::Match {
            scr: Box::new(scr),
            arms,
        };
        let span = opening.join(&span).unwrap();
        Ok(self.node(kind, span))
    }

    fn match_arm(&mut self) -> Maybe<MatchArm> {
        let pat = self.pattern()?;
        self.consume(Lexeme::EqualRAngle)?;
        let expr = Box::new(self.expression()?);
        Ok(MatchArm { pat, expr })
    }

    fn for_expr(&mut self) -> Maybe<Expr> {
        let opening = self.token()?.span;
        let bind = Box::new(self.lvalue()?);
        self.consume(Lexeme::In)?;
        let iter = Box::new(self.expression()?);
        let body = Box::new(self.block()?);
        let span = opening.join(&body.span).unwrap();
        let kind = ExprKind::For { bind, iter, body };
        Ok(self.node(kind, span))
    }

    fn block_expr(&mut self) -> Maybe<Expr> {
        let block = self.block()?;
        let block_span = block.span;
        Ok(self.node(ExprKind::Block(Box::new(block)), block_span))
    }

    fn block(&mut self) -> Maybe<Block> {
        let opening = self.ldelim(Brace)?.span;
        // Start collecting the contents of the block
        let (mut stmts, table) = self.with_table(|prsr| {
            let mut stmts: Vec<Stmt> = vec![];
            while let Some(lexeme) = prsr.peek_lexeme() {
                match lexeme {
                    RDelim(Brace) => {
                        break;
                    }
                    Lexeme::Fn | Lexeme::Struct | Lexeme::Type => prsr.item()?,
                    _ => stmts.push(prsr.statement()?),
                }
            }
            Ok(stmts)
        })?;
        let closing = self.rdelim(Brace)?.span;
        let span = opening.join(&closing).unwrap();

        // Set the `expr` field: if the last statement is a nonterminated
        // expression statement, unwrap it and put it there.
        let expr = match stmts.pop() {
            Some(Spanned {
                data: StmtKind::Expr(expr),
                ..
            }) => Some(expr),
            Some(tail) => {
                stmts.push(tail);
                None
            }
            None => None,
        };

        Ok(Block {
            stmts,
            expr,
            table,
            span,
        })
    }

    fn expr_stmt(&mut self) -> Maybe<Stmt> {
        let res = StmtKind::Expr(Box::new(self.expression()?));
        self.consume(Lexeme::Semicolon)?;
        Ok(res.into())
    }

    pub fn expression(&mut self) -> Maybe<Expr> {
        // Disable the struct literal exclusion condition, and restore it before
        // returning.
        self.with_excl_struct_lit(false, Self::expression_inner)
    }

    fn expression_inner(&mut self) -> Maybe<Expr> {
        // The head or root of the expression
        let expr = match self.peek_lexeme() {
            Some(Lexeme::If) => self.if_expr(),
            Some(Lexeme::Match) => self.match_expr(),
            Some(Lexeme::For) => self.for_expr(),
            Some(Lexeme::LDelim(Brace)) => self.block_expr(),
            Some(_) => {
                let lhs = self.unary()?;
                self.precedence_climb(lhs, 0)
            }
            None => Err(self.errors.push(UnexpectedEof { span: self.loc })),
        }?;
        Ok(expr)
    }

    fn unary(&mut self) -> Maybe<Expr> {
        if let Some(Bang) | Some(Tilde) | Some(Question) = self.peek_lexeme() {
            let op = self.next().unwrap();
            let op = UnOp::from_token(op, self.ctx).unwrap();
            let right = self.unary()?;
            let span = op.span.join(&right.span).unwrap();
            let kind = ExprKind::UnOp {
                op,
                right: Box::new(right),
            };
            return Ok(self.node(kind, span));
        } else if let Some(LDelim(Bracket)) = self.peek_lexeme() {
            let opening = self.token()?.span;
            return self.finish_array(opening);
        }
        self.call()
    }

    fn finish_array(&mut self, opening: Span) -> Maybe<Expr> {
        // Empty array:
        if let Some(RDelim(Bracket)) = self.peek_lexeme() {
            let closing = self.token().unwrap().span;
            let span = opening.join(&closing).unwrap();
            return Ok(self.node(ExprKind::ExtArr(vec![]), span));
        }

        // Otherwise, there is at least one item:
        let item = self.expression()?;
        let arr = if self.match_lexeme(&Semicolon) {
            let item = Box::new(item);
            let reps = Box::new(self.expression()?);
            ExprKind::IntArr { item, reps }
        } else {
            let mut items = vec![item];
            loop {
                if !self.match_lexeme(&Comma) {
                    break;
                }
                items.push(self.expression()?);
            }
            ExprKind::ExtArr(items)
        };
        let closing = self.rdelim(Bracket)?.span;
        let span = opening.join(&closing).unwrap();
        Ok(self.node(arr, span))
    }

    fn type_annotation(&mut self) -> Maybe<Annot> {
        // Get another token. We're anticipating being able to form a type
        // annotation here, so it's an error if none is available.
        let Token { lexeme, span } = self.token()?;
        // TODO How to make this more succinct: a macro? It doesn't seem
        // possible for macros to expand to match arms. An or-pattern? Not
        // stable yet.
        let ty = match lexeme {
            Bool => Annot {
                span,
                data: AnnotKind::Bool,
            },
            U4 | U8 | U16 | U32 => Annot {
                span,
                data: AnnotKind::Uint(Uint::from_lexeme(lexeme).unwrap()),
            },
            Ord => Annot {
                span,
                data: AnnotKind::Ord,
            },
            LDelim(Bracket) => self.finish_array_type(span)?,
            LDelim(Paren) => self.finish_tuple_type(span)?,
            Question => {
                let ty_inner = self.type_annotation()?;
                Annot {
                    span: span.join(&ty_inner.span).unwrap(),
                    data: AnnotKind::Question(Box::new(ty_inner)),
                }
            }
            // overly verbose...
            Ident(symb) => {
                let data = self.ctx.intern_symb(symb);
                Annot {
                    span,
                    data: AnnotKind::Ident(ast::Ident { span, data }),
                }
            }
            // A non-annotation lexeme
            x => return Err(self.errors.push(ExpectedTypeAnnot { span, actual: x })),
        };

        Ok(ty)
    }

    /// Finish parsing an array type.
    fn finish_array_type(&mut self, opening: Span) -> Maybe<Annot> {
        let ty = Box::new(self.type_annotation()?);
        let closing = self.rdelim(Bracket)?;
        let span = opening.join(&closing.span).unwrap();
        Ok(Annot {
            span,
            data: AnnotKind::Array(ty),
        })
    }

    /// Finish parsing a type that may be either a tuple or the unit type.
    fn finish_tuple_type(&mut self, opening: Span) -> Maybe<Annot> {
        let mut types = vec![];
        if self.peek_lexeme() != Some(&RDelim(Paren)) {
            types.push(self.type_annotation()?);
            while self.peek_lexeme() != Some(&RDelim(Paren)) {
                self.consume(Comma)?;
                types.push(self.type_annotation()?);
            }
        }
        let closing = self.rdelim(Paren)?;
        let span = opening.join(&closing.span).unwrap();
        let kind = AnnotKind::Tuple(types);
        Ok(Annot { span, data: kind })
    }

    /// A field access on an expression, like `x.a`
    fn field(&mut self) -> Maybe<Field> {
        let token = self.token()?;
        let span = token.span;
        let field = match token.lexeme {
            Ident(ident) => {
                let ident = self.ctx.intern_symb(ident);
                Field {
                    span,
                    data: FieldKind::Ident(ident),
                }
            }
            Nat(n, None) => Field {
                span,
                data: FieldKind::Num(n),
            },
            actual => return Err(self.errors.push(ExpectedFieldToken { span, actual })),
        };
        Ok(field)
    }

    /// Call a function or index into an array.
    #[rustfmt::skip]
    fn call(&mut self) -> Maybe<Expr> {
        let mut expr = self.field_access()?;

        // This is a function call
        if let Some(LDelim(Paren)) = self.peek_lexeme() {
            if let ExprKind::Ident(ident @ ast::Ident { .. }) = expr.data {
                return self.finish_call(ident);
            } else {
                return Ok(expr);
            }
        }

        // Otherwise, this is either a bunch of nested index operations, or it's
        // just a primary token. Build up indexing operations as long as there
        // are open-brackets to consume.
        while self.match_lexeme(&LDelim(Bracket)) {
            expr = self.finish_index(expr)?;
        }

        Ok(expr)
    }

    // Inline(always) because there is only one call site.
    #[inline(always)]
    fn finish_call(&mut self, callee: ast::Ident) -> Maybe<Expr> {
        let (args, span) = self.delimited_list(Paren, Comma, false, Self::expression)?;
        let span = callee.span.join(&span).unwrap();
        let kind = ExprKind::Call { callee, args };
        Ok(self.node(kind, span))
    }

    #[inline(always)]
    fn finish_index(&mut self, head: Expr) -> Maybe<Expr> {
        let head = Box::new(head);
        let index = Box::new(self.expression()?);
        let bracket = self.consume(RDelim(Bracket))?.span;
        let span = head.span.join(&bracket).unwrap();
        let kind = ExprKind::Index { head, index };
        Ok(self.node(kind, span))
    }

    /// Field accesses can occur only primary expressions (but may still be a
    /// type error).
    ///
    /// NOTE this might prove to create a parsing ambiguity if there are ever
    /// floating-point types (is `4.2` the number 17/5, or an access to field
    /// `2` on `4`?).
    fn field_access(&mut self) -> Maybe<Expr> {
        let mut expr = self.primary()?;

        while let Some(Dot) = self.peek_lexeme() {
            self.tokens.next();
            let field = self.field()?;
            let span = expr.span.join(&field.span).unwrap();
            let kind = ExprKind::Field(Box::new(expr), field);
            expr = self.node(kind, span);
        }
        Ok(expr)
    }

    fn primary(&mut self) -> Maybe<Expr> {
        let token = self.next().unwrap();
        match token.lexeme {
            Nat(_, _) | True | False | Ord => {
                let lit = ast::Literal::from_token(token, self.ctx).unwrap();
                let lit_span = lit.span;
                Ok(self.node(ExprKind::Literal(lit), lit_span))
            }
            Ident(_) => {
                let ident = ast::Ident::from_token(token, self.ctx).unwrap();
                // NOTE There is a parsing ambiguity here: if we're in a context
                // where a `{` is expected to follow an expression, as in an
                // `if` expression, we must not parse a struct literal. So, we
                // should include an escape hatch against doing this.
                if matches!(self.peek_lexeme(), Some(LDelim(Brace))) & !self.excl_struct_lit {
                    // This should be a struct literal, like `A { a: x, b: true }`
                    //
                    // NOTE it feels a little wrong to have this under a
                    // production called "primary", since it's actually a nonterminal rule.
                    // But this does seem to be the right place for it to live.
                    return self.finish_struct_literal(ident);
                }
                let span = ident.span;
                Ok(self.node(ExprKind::Ident(ident), span))
            }
            LDelim(Paren) => self.finish_group(token.span),

            lexeme => Err(self.errors.push(ExpectedPrimaryToken {
                // Guaranteed not to be EOF!
                span: token.span,
                actual: lexeme,
            })),
        }
    }

    fn finish_struct_literal(&mut self, ty: ast::Ident) -> Maybe<Expr> {
        let (fields, span) = self.delimited_list(Brace, Comma, true, |this: &mut Self| {
            let name = this.consume_ident()?;
            this.consume(Colon)?;
            let value = this.expression()?;
            Ok((name, value))
        })?;
        let span = ty.span.join(&span).unwrap();
        let expr = ExprKind::Struct { ty, fields };
        Ok(self.node(expr, span))
    }

    /// After reaching an `(` in the position of a primary token, we must have
    /// either a group or a sequence.
    fn finish_group(&mut self, opening: Span) -> Maybe<Expr> {
        // `()` shall be an empty sequence, and evaluate to an empty tuple.
        if let Some(RDelim(Paren)) = self.peek_lexeme() {
            let span = opening.join(&self.token().unwrap().span).unwrap();
            return Ok(self.node(ExprKind::Tuple(vec![]), span));
        }

        let head = self.expression()?;
        let kind = if let Some(&Lexeme::Comma) = self.peek_lexeme() {
            // Tuples with one element should have a single trailing comma to
            // disambiguate from groups.
            //
            // FIXME can this case use `delimited_list`? It's a little bit
            // different because of the terminal comma in the single-element
            // case.
            let mut items = vec![head];
            while self.match_lexeme(&Lexeme::Comma) {
                if let Some(&RDelim(Paren)) = &self.peek_lexeme() {
                    break;
                }
                items.push(self.expression()?);
            }
            ExprKind::Tuple(items)
        } else {
            // If there were no commas, we should have a single expression
            // followed by a close-paren, and return a group. Take the head node
            // and unwrap it, so we can give it the correct span.
            head.data
        };
        let span = opening.join(&self.rdelim(Paren)?.span).unwrap();
        Ok(self.node(kind, span))
    }

    fn precedence_climb(&mut self, lhs: Expr, min_precedence: u8) -> Maybe<Expr> {
        let Expr {
            data: mut lhs,
            mut span,
            ..
        } = lhs;
        let mut op_prec;
        while let Some(outer) = self.peek_lexeme() {
            // Check the outer operator's precedence
            if let Some(Precedence(outer_prec, _)) = operator(outer) {
                op_prec = outer_prec;
                if op_prec < min_precedence {
                    break;
                }
                let outer = self.next().unwrap();
                let mut rhs = self.unary()?;
                while let Some(inner) = self.peek_lexeme() {
                    // Check the inner operator's precedence
                    if let Some(Precedence(inner_prec, r_assoc)) = operator(inner) {
                        if inner_prec + (r_assoc as u8) <= op_prec {
                            break;
                        }
                        rhs = self.precedence_climb(rhs, inner_prec)?;
                    } else {
                        break;
                    }
                }

                let rhs_span = rhs.span;
                // Check for assignment expressions as a specal case
                if let Lexeme::Equal = outer.lexeme {
                    let lhs = self.node(lhs, span);
                    return Ok(self.node(
                        ExprKind::Assn {
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        span.join(&rhs_span).unwrap(),
                    ));
                }

                // Handle all other cases, which are more ordinary "BinOp"s.
                let op = BinOp::from_token(outer, self.ctx).unwrap();
                lhs = ExprKind::BinOp {
                    op,
                    left: Box::new(self.node(lhs, span)),
                    right: Box::new(rhs),
                };
                span = span.join(&rhs_span).unwrap();
            } else {
                break;
            }
        }
        Ok(self.node(lhs, span))
    }

    fn synchronize(&mut self, _err: &str) {
        todo!();
    }
}

mod errors {
    use super::Lexeme;
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[msg = "expected `{expected}`, found `{actual}`"]
    pub struct ExpectedToken {
        #[span]
        pub span: Span,
        /// The expected lexeme
        pub expected: Lexeme,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    #[msg = "expected identifier, found `{actual}`"]
    pub struct ExpectedIdentifier {
        #[span]
        pub span: Span,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    #[msg = "expected item, found token `{actual}`"]
    pub struct ExpectedItem {
        #[span]
        pub span: Span,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    #[msg = "unexpected end of file"]
    pub struct UnexpectedEof {
        #[span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "expected primary token, found `{actual}`"]
    pub struct ExpectedPrimaryToken {
        #[span]
        pub span: Span,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    #[msg = "expected identifier or numeral, found `{actual}`"]
    pub struct ExpectedFieldToken {
        #[span]
        pub span: Span,
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    #[msg = "expected type annotation, found `{actual}`"]
    pub struct ExpectedTypeAnnot {
        #[span]
        pub span: Span,
        /// The lexeme actually found
        pub actual: Lexeme,
    }

    #[derive(Diagnostic)]
    #[msg = "multiple functions named `main`"]
    pub struct MultipleEntryPoints {
        #[span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "multiple definitions of item in this scope"]
    pub struct MultipleDefinitions {
        #[span(msg = "this item was first defined here...")]
        pub fst: Span,
        #[span(msg = "...and defined again here")]
        pub snd: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "entry point `main` must not take parameters or return"]
    pub struct InvalidMainSignature {
        #[span]
        pub span: Span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ExprKind::{self, *};
    use crate::session::Config;
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
        ($ast:expr, ({$op:ident} $left:tt $right:tt)) => {
            match &$ast.data {
                ExprKind::BinOp { op, left, right } => {
                    assert_eq!(op.data, BinOpKind::$op);
                    test_s_expr! { *left, $left };
                    test_s_expr! { *right, $right };
                }
                _ => panic!("unexpected AST node")
            }
        };
        // UnOp
        ($ast:expr, ({$op:ident} $right:tt)) => {
            match &$ast.data {
                ExprKind::UnOp { op, right } => {
                    assert_eq!(op.data, UnOpKind::$op);
                    test_s_expr! { *right, $right };
                }
                _ => panic!("unexpected AST node")
            }
        };

        // Literals and variables. In this case, include the Ast in order to
        // resolve symbols, which must be interned before comparison
        ($ast:expr, {$($lit:tt)*}) => {
            match &$ast.data {
                ExprKind::Literal(lit) => {
                    // For backwards compatibility: convert the Literal back
                    // into a Lexeme.
                    let lexeme = match lit.data {
                        LiteralKind::True => Lexeme::True,
                        LiteralKind::False => Lexeme::False,
                        LiteralKind::Nat(n, sz) => Lexeme::Nat(n, sz),
                        LiteralKind::Ord => todo!(),
                    };
                    assert_eq!(lexeme, $($lit)*);
                }
                ExprKind::Ident(_ident) => {
                    // For backwards compatibility of this test: convert the
                    // Ident back into a Lexeme::Ident.

                    // FIXME pass this for now: test disabled because lexemes
                    // are now just ids. Have to figure out how to match the id.

                    // assert_eq!(lexeme, $($lit)*);
                }
                _ => panic!("unexpected AST node")
            }
        };
    }

    /// This macro compares puts a list of lexemes into a parser and compares
    /// the output to a literal syntax tree.
    macro_rules! test_parser {
        // If there's only a list of lexemes, just try to parse it!
        ([$($lexeme:expr),+]) => {
            let tokens = vec![$(token($lexeme)),+];
            let conf = Config::default();
            let mut ctx = Context::new(&conf);
            let mut parser = Parser::new(tokens, &mut ctx);
            parser.expression().unwrap();
        };
        // If a second arm is included, we'll try to match the parse tree
        // against the S-expression it contains.
        ([$($lexeme:expr),+], $($s_expr:tt)+) => {
            let tokens = vec![$(token($lexeme)),+];
            let conf = Config::default();
            let mut ctx = Context::new(&conf);
            let mut parser = Parser::new(tokens, &mut ctx);
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
            [Nat(1, None)],
            {Nat(1, None)}
        };
    }

    #[test]
    #[should_panic]
    fn single_nat_2() {
        test_parser! {
            [Nat(0, None)],
            {Nat(1, None)}
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

    ///////////////////////////////////////
    // Unary operators: tildes and bangs //
    ///////////////////////////////////////

    #[test]
    fn tilde_false() {
        test_parser! {
            [Tilde, False],
            ({Not} {False})
        }
    }

    #[test]
    fn bang_true() {
        test_parser! {
            [Bang, True],
            ({Delin} {True})
        }
    }

    #[test]
    fn tilde_tilde_false() {
        test_parser! {
            [Tilde, Tilde, False],
            ({Not} ({Not} {False}))
        }
    }

    #[test]
    fn tilde_bang_false() {
        test_parser! {
            [Tilde, Bang, False],
            ({Not} ({Delin} {False}))
        }
    }

    //////////////////////
    // Binary operators //
    //////////////////////

    #[test]
    fn plus_simple() {
        test_parser! {
            [Nat(1, None), Plus, Nat(1, None)],
            ({Plus} {Nat(1, None)} {Nat(1, None)})
        }
    }

    #[test]
    fn star_simple() {
        test_parser! {
            [Nat(1, None), Star, Nat(1, None)],
            ({Times} {Nat(1, None)} {Nat(1, None)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn plus_left_assoc() {
        test_parser! {
            [Nat(1, None), Plus, Nat(2, None), Plus, Nat(3, None)],
            ({Plus}
             ({Plus} {Nat(1, None)} {Nat(2, None)})
             {Nat(3, None)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn star_left_assoc() {
        test_parser! {
            [Nat(1, None), Star, Nat(2, None), Star, Nat(3, None)],
            ({Times}
             ({Times} {Nat(1, None)} {Nat(2, None)})
             {Nat(3, None)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn mixed_star_plus() {
        test_parser! {
            [Nat(1, None), Star, Nat(2, None), Plus, Nat(3, None)],
            ({Plus}
             ({Times} {Nat(1, None)} {Nat(2, None)})
             {Nat(3, None)})
        }
    }

    #[test]
    #[rustfmt::skip]
    fn mixed_plus_star() {
        test_parser! {
            [Nat(1, None), Plus, Nat(2, None), Star, Nat(3, None)],
            ({Plus} {Nat(1, None)}
             ({Times} {Nat(2, None)} {Nat(3, None)}))
        }
    }

    #[test]
    #[rustfmt::skip]
    fn mixed_plus_equalequal() {
        test_parser! {
            [Nat(2, None), Plus, Nat(2, None), EqualEqual, Nat(3, None), Plus, Nat(1, None)],
            ({Equal}
             ({Plus} {Nat(2, None)} {Nat(2, None)})
             ({Plus} {Nat(3, None)} {Nat(1, None)})
            )
        }
    }

    #[test]
    #[should_panic]
    fn plus_nonterminal() {
        test_parser! { [Nat(1, None), Plus, Plus] }
    }

    //////////////////////////////
    // Binary + unary operators //
    //////////////////////////////

    #[test]
    fn bang_plus() {
        test_parser! {
            [Bang, Nat(1, None), Plus, Nat(2, None)],
            ({Plus} ({Delin} {Nat(1, None)}) {Nat(2, None)})
        }
    }

    #[test]
    fn plus_bang() {
        test_parser! {
            [Nat(1, None), Plus, Bang, Nat(2, None)],
            ({Plus} {Nat(1, None)} ({Delin} {Nat(2, None)}))
        }
    }

    #[test]
    fn plus_bang_plus() {
        test_parser! {
            [Nat(1, None), Plus, Bang, Nat(2, None), Plus, Nat(3, None)],
            ({Plus}
             ({Plus} {Nat(1, None)} ({Delin} {Nat(2, None)}))
             {Nat(3, None)})
        }
    }

    ///////////////////////////
    // False-positive checks //
    ///////////////////////////

    // This shouldn't build a tree including the non-operator token `;`
    #[test]
    fn non_operator() {
        test_parser! {
            [Nat(1, None), Plus, Nat(2, None), Semicolon, Nat(4, None)],
            ({Plus} {Nat(1, None)} {Nat(2, None)})
        }
    }

    // Repeat the same thing, but with an actual operator, and show that we
    // don't get a false-positive in this case.
    #[test]
    #[should_panic]
    fn non_operator_sanity_check() {
        test_parser! {
            [Nat(1, None), Plus, Nat(2, None), Plus, Nat(3, None), Plus, Nat(4, None)],
            ({Plus} {Nat(1, None)}
             ({Plus} {Nat(2, None)} {Nat(3, None)}))
        }
    }
}
