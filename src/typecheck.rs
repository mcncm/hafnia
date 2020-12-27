use crate::ast::{Expr, ExprKind, Item, ItemKind, LValue, Stmt, StmtKind};
use crate::errors::ErrorBuf;
use crate::functions::{Func, UserFunc};
use crate::types::Type;
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// Run a type-checking pass, annotating the AST as you go, and return a valid
/// symbol table. For now, this is the single entry point for all semantic
/// analysis passes, not just type-checking proper. It will also mutate the AST,
/// adding type annotations where necessary (or possible).
pub fn typecheck(stmts: &mut Vec<Stmt>) -> Result<SymbolTable, ErrorBuf> {
    let mut root = SymbolTable::default();
    hoist_items(stmts);
    for stmt in stmts.iter_mut() {
        type_stmt(stmt, &mut root)?;
    }
    Ok(root)
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

/// Typecheck a statement. This will be executed after hoisting, so all items
/// will have been hoisted to the top.
fn type_stmt<'ast>(stmt: &'ast Stmt, table: &mut SymbolTable<'ast>) -> Result<(), ErrorBuf> {
    use StmtKind::*;
    match &stmt.kind {
        // No-op
        Print(_expr) => {}
        // An expression statement not decorated with a semicolon: could be a
        // return value from a block.
        Expr(expr) => type_expr(expr, table)?,
        // An expression statement decorated with a semicolon
        ExprSemi(expr) => type_expr(expr, table)?,
        // A new local binding: insert the name into the symbol table
        Local { lhs, ty, rhs } => table.insert_local(lhs, ty, rhs),
        // All these are expected to be at the top of the AST, as they’ve
        // already been hoisted.
        Item(item) => table.insert_item(item),
    };
    Ok(())
}

/// Typecheck a single expression
fn type_expr(_expr: &Expr, _table: &mut SymbolTable) -> Result<(), ErrorBuf> {
    Ok(())
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

#[derive(Default)]
pub struct SymbolTable<'ast> {
    /// For now, there is a single namespace for all symbols. It might be better
    /// to have separate namespaces for functions, variables, types, and so on.
    symbols: HashMap<&'ast str, Symbol>,
    parent: Option<Weak<SymbolTable<'ast>>>,
}

impl<'ast> SymbolTable<'ast> {
    fn insert_item(&mut self, item: &'ast Item) {
        match &item.kind {
            ItemKind::Fn {
                name,
                params: _params,
                typ,
                body,
                docstring,
            } => {
                let _ty = typ.as_ref().unwrap_or(&Type::T_Unit);
                let func = Box::new(UserFunc {
                    params: vec![],
                    // FIXME temporarily defeating the borrow checker
                    body: body.clone(),
                    doc: docstring.clone(),
                });
                let symb = Symbol {
                    ty: Type::T_Unit,
                    kind: SymbolKind::Fn(func),
                };
                self.symbols.insert(&name, symb);
            }
        }
    }

    fn insert_local(&mut self, _lhs: &LValue, _ty: &Option<Box<Type>>, _rhs: &Expr) {}
}
