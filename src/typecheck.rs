use crate::ast::*;
use crate::cavy_errors::{Diagnostic, ErrorBuf};
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
            self.type_stmt(stmt, &mut root);
        }

        if self.errors.is_empty() {
            Ok(root)
        } else {
            Err(self.errors)
        }
    }

    /// Typecheck a statement. This will be executed after hoisting, so all items
    /// will have been hoisted to the top.
    fn type_stmt<'ast>(
        &mut self,
        stmt: &'ast Stmt,
        table: &mut SymbolTable<'ast>,
    ) -> Result<(), ()> {
        use StmtKind::*;
        match &stmt.kind {
            // No-op
            Print(_expr) => Ok(()),
            // An expression statement not decorated with a semicolon: could be a
            // return value from a block.
            Expr(expr) => self.type_expr(expr, table),
            // An expression statement decorated with a semicolon
            ExprSemi(expr) => self.type_expr(expr, table),
            // A new local binding: insert the name into the symbol table
            Local { lhs, ty, rhs } => {
                let ty = self.type_local(lhs, ty, rhs)?;
                table.insert_local(lhs, ty);
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
    fn type_expr(&self, _expr: &Expr, _table: &mut SymbolTable) -> Result<(), ()> {
        Ok(())
    }

    fn type_local(&self, lhs: &LValue, ty: &Option<Annot>, rhs: &Expr) -> Result<Type, ()> {
        todo!();
    }

    fn resolve_annot(&self, annot: &Annot, table: &SymbolTable) -> Result<Type, ()> {
        let ty = match &annot.kind {
            AnnotKind::Bool => Type::Bool,
            AnnotKind::U8 => Type::U8,
            AnnotKind::U16 => Type::U16,
            AnnotKind::U32 => Type::U32,

            AnnotKind::Tuple(_inners) => {
                // let inner_types = inners
                //     .iter()
                //     .map(|ann| self.resolve_annot(ann))
                //     .collect::<Vec<Type>>()?;
                // Type::Tuple(inner_types)
                todo!()
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

    fn resolve_annot_question(&self, inner: Type, table: &SymbolTable) -> Result<Type, ()> {
        let ty = match inner {
            Type::Bool => Type::Q_Bool,
            Type::U8 => Type::Q_U8,
            Type::U16 => Type::Q_U16,
            Type::U32 => Type::Q_U32,

            _ => unimplemented!(),
        };
        Ok(ty)
    }

    fn resolve_annot_bang(&self, inner: Type) -> Result<Type, ()> {
        todo!()
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

    fn insert_local(&mut self, lhs: &LValue, ty: Type) {
        todo!();
    }
}

mod errors {
    use crate::cavy_errors::Diagnostic;
    use crate::source::Span;
    use cavy_macros::Diagnostic;
}
