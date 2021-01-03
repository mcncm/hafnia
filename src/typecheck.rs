use crate::ast::*;
use crate::cavy_errors::{CavyError, Diagnostic, ErrorBuf, Result};
use crate::functions::{Func, UserFunc};
use crate::session::Session;
use crate::types::Type;
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// Main entry point for the semantic analysis phase.
///
/// Run a type-checking pass, annotating the AST as you go, and return a valid
/// symbol table. For now, this is the single entry point for all semantic
/// analysis passes, not just type-checking proper. It will also mutate the AST,
/// adding type annotations where necessary (or possible).
pub fn typecheck<'s>(stmts: &'s mut Vec<Stmt>, sess: &'s Session) -> SymbolTable<'s> {
    use crate::session::Phase;
    let last_phase = sess.config.phase_config.last_phase;
    if last_phase < Phase::Typecheck {
        crate::sys::exit(0);
    }

    let tc = Typechecker::new(sess);
    match tc.typecheck(stmts) {
        Ok(root) => root,
        Err(errs) => {
            sess.emit_diagnostics(errs);
            crate::sys::exit(1);
        }
    }
}

/// This struct handles essentially all of the semantic analysis passes; the
/// name might be a little misleading. However, its main job is to produce a
/// well-typed symbol table.
pub struct Typechecker<'s> {
    sess: &'s Session,
    errors: ErrorBuf,
}

impl<'s> Typechecker<'s> {
    pub fn new(sess: &'s Session) -> Self {
        Self {
            sess,
            errors: ErrorBuf::new(),
        }
    }

    pub fn typecheck(
        mut self,
        stmts: &mut Vec<Stmt>,
    ) -> std::result::Result<SymbolTable, ErrorBuf> {
        let mut root = SymbolTable::new();
        hoist_items(stmts);
        for stmt in stmts.iter_mut() {
            let _ = self.type_stmt(stmt, &mut root);
        }

        if self.errors.is_empty() {
            Ok(root)
        } else {
            Err(self.errors)
        }
    }

    /// Typecheck a statement. This will be executed after hoisting, so all items
    /// will have been hoisted to the top.
    fn type_stmt<'ast>(&mut self, stmt: &'ast Stmt, table: &mut SymbolTable<'ast>) -> Result<()> {
        use StmtKind::*;
        match &stmt.kind {
            // No-op
            Print(_expr) => Ok(()),
            // An expression statement not decorated with a semicolon: could be a
            // return value from a block.
            Expr(expr) => self.type_expr(expr, table).map(|_| ()),
            // An expression statement decorated with a semicolon
            ExprSemi(expr) => self.type_expr(expr, table).map(|_| ()),
            // A new local binding: insert the name into the symbol table
            Local { lhs, ty, rhs } => {
                let ty = self.type_local(ty, rhs, table)?;
                self.insert_local(lhs, ty, table);
                Ok(())
            }
            // All these are expected to be at the top of the AST, as they’ve
            // already been hoisted.
            Item(item) => {
                table.insert_item(item);
                Ok(())
            }
        }
    }

    /// Typecheck a single expression
    fn type_expr(&mut self, expr: &Expr, table: &SymbolTable) -> Result<Type> {
        match &expr.kind {
            ExprKind::BinOp { left, op, right } => self.type_binop(left, op, right, table),
            ExprKind::UnOp { op, right } => self.type_unop(op, right, table),
            ExprKind::Literal(lit) => self.type_literal(lit, table),
            ExprKind::Tuple(vals) => self.type_tuple(vals, table),
            _ => unimplemented!(),
        }
    }

    fn type_binop(
        &mut self,
        left: &Box<Expr>,
        op: &BinOp,
        right: &Box<Expr>,
        table: &SymbolTable,
    ) -> Result<Type> {
        use BinOpKind::*;
        use Type::*;
        let ty_l = self.type_expr(left, table)?;
        let ty_r = self.type_expr(right, table)?;
        let ty = match (op.kind, ty_l, ty_r) {
            // These are not quite right!
            (Equal, l, r) if l == r => l,
            (Nequal, l, r) if l == r => l,

            (Plus, U8, U8) => U8,
            (Plus, U16, U16) => U16,
            (Plus, U32, U32) => U32,

            (Plus, Q_U8, Q_U8) => U8,
            (Plus, Q_U16, Q_U16) => U16,
            (Plus, Q_U32, Q_U32) => U32,

            (kind, left, right) => {
                return Err(self.errors.push(errors::BinOpTypeError {
                    span: op.span,
                    kind,
                    left,
                    right,
                }));
            }
        };
        Ok(ty)
    }

    fn type_unop(&mut self, _op: &UnOp, _right: &Box<Expr>, _table: &SymbolTable) -> Result<Type> {
        todo!();
    }

    fn type_tuple(&mut self, vals: &Vec<Expr>, table: &SymbolTable) -> Result<Type> {
        let tys = vals
            .iter()
            .map(|v| self.type_expr(v, table))
            // NOTE: this short-circuits at the first error, which is really not
            // quite the behavior I want.
            .collect::<Result<Vec<Type>>>()?;
        Ok(Type::Tuple(tys))
    }

    fn type_local(&mut self, _ty: &Option<Annot>, rhs: &Expr, table: &SymbolTable) -> Result<Type> {
        let ty_r = self.type_expr(rhs, table)?;
        Ok(ty_r)
    }

    fn resolve_annot(&self, annot: &Annot, table: &SymbolTable) -> Result<Type> {
        let ty = match &annot.kind {
            AnnotKind::Bool => Type::Bool,
            AnnotKind::U8 => Type::U8,
            AnnotKind::U16 => Type::U16,
            AnnotKind::U32 => Type::U32,

            AnnotKind::Tuple(inners) => {
                let inner_types = inners
                    .iter()
                    .map(|ann| self.resolve_annot(ann, table))
                    .collect::<Result<Vec<Type>>>()?;
                Type::Tuple(inner_types)
            }
            AnnotKind::Array(inner) => {
                let ty = Box::new(self.resolve_annot(inner, table)?);
                Type::Array(ty)
            }

            AnnotKind::Question(inner) => {
                let ty = self.resolve_annot(inner, table)?;
                self.resolve_annot_question(ty, table)?
            }

            AnnotKind::Bang(inner) => {
                let ty = self.resolve_annot(inner, table)?;
                self.resolve_annot_bang(ty)?
            }

            AnnotKind::Ident(_ident) => {
                todo!()
            }
        };

        Ok(ty)
    }

    fn type_literal(&mut self, lit: &Literal, _table: &SymbolTable) -> Result<Type> {
        use LiteralKind::*;
        use Type::*;
        match lit.kind {
            True => Ok(Bool),
            False => Ok(Bool),
            Nat(_) => Ok(U32),
        }
    }

    fn resolve_annot_question(&self, inner: Type, _table: &SymbolTable) -> Result<Type> {
        let ty = match inner {
            Type::Bool => Type::Q_Bool,
            Type::U8 => Type::Q_U8,
            Type::U16 => Type::Q_U16,
            Type::U32 => Type::Q_U32,

            _ => unimplemented!(),
        };
        Ok(ty)
    }

    fn resolve_annot_bang(&self, _inner: Type) -> Result<Type> {
        todo!()
    }

    /// Insert local bindings, recursively destructuring the LValue and type
    fn insert_local(&mut self, lhs: &LValue, ty: Type, table: &mut SymbolTable) -> Result<()> {
        match (&lhs.kind, &ty) {
            (LValueKind::Tuple(lvalues), Type::Tuple(tys)) => {
                if lvalues.len() != tys.len() {
                    return Err(self.errors.push(errors::DestructuringError {
                        span: lhs.span,
                        actual: ty,
                    }))?;
                }

                for (lvalue, ty) in lvalues.iter().zip(tys.into_iter()) {
                    // FIXME: this clone shouldn't be necessary, right? Why is
                    // `into_iter` not yielding owned `Type`s here?
                    self.insert_local(lvalue, ty.clone(), table)?;
                }
            }
            (LValueKind::Ident(ident), _) => {
                todo!();
            }
            _ => todo!(),
        };
        Ok(())
    }
}

/// Hoists `fn`, `struct`, `enum` declarations to the top of a list of
/// statements, but does not insert them in a symbol table.
fn hoist_items(stmts: &mut Vec<Stmt>) {
    // `Vec::sort_by` is a stable sort, so all this will do is carry items to
    // the top, without reordering anything else. This significantly simplifies
    // the implementation, at least as long as `drain_filter` is unstable.
    stmts.sort_by(|left, right| {
        let left = left.kind.is_item();
        let right = right.kind.is_item();
        left.cmp(&right)
    });
}

/// Lives in symbol table, carries type, lifetime information and so on.
pub struct Symbol {
    kind: SymbolKind,
    ty: Type,
}

pub enum SymbolKind {
    Fn(Box<dyn Func>),
    Var,
}

pub struct SymbolTable<'ast> {
    /// For now, there is a single namespace for all symbols. It might be better
    /// to have separate namespaces for functions, variables, types, and so on.
    symbols: HashMap<&'ast str, Symbol>,
    parent: Option<Weak<SymbolTable<'ast>>>,
}

impl<'ast> SymbolTable<'ast> {
    fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            parent: None,
        }
    }

    fn insert_item(&mut self, item: &'ast Item) {
        match &item.kind {
            ItemKind::Fn {
                name,
                params: _,
                typ: _,
                body,
                docstring,
            } => {
                let func = Box::new(UserFunc {
                    params: vec![],
                    // FIXME temporarily defeating the borrow checker
                    body: body.clone(),
                    doc: docstring.clone(),
                });
                let symb = Symbol {
                    ty: Type::unit(),
                    kind: SymbolKind::Fn(func),
                };
                self.symbols.insert(&name, symb);
            }
        }
    }
}

mod errors {
    use crate::ast::*;
    use crate::cavy_errors::Diagnostic;
    use crate::source::Span;
    use crate::types::Type;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    pub struct BinOpTypeError {
        #[msg = "operator `{kind}` doesn't support argument types `{left}` and `{right}`"]
        pub span: Span,
        /// The operator
        pub kind: BinOpKind,
        /// The actual left operand type
        pub left: Type,
        /// The actual right operand type
        pub right: Type,
    }

    #[derive(Diagnostic)]
    pub struct UnOpTypeError {
        #[msg = "operator `{kind}` doesn't support argument type `{actual}`"]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual left operand type
        pub actual: Type,
    }

    #[derive(Diagnostic)]
    pub struct DestructuringError {
        #[msg = "pattern fails to match type `{actual}`"]
        pub span: Span,
        /// The type
        pub actual: Type,
    }
}
