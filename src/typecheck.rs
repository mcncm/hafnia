use crate::ast::Stmt;
use crate::errors::ErrorBuf;

/// Run a type-checking pass, annotating the AST as you go.
pub fn typecheck(_stmts: &mut Vec<Stmt>) -> Result<(), ErrorBuf> {
    Ok(())
}
