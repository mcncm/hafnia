use crate::ast::{self, *};
use crate::cavy_errors::{CavyError, Diagnostic, ErrorBuf, Result};
// use crate::functions::{Func, UserFunc};
use crate::context::Context;
use crate::{
    mir::{self, *},
    store::Index,
    types::{TyId, Type},
};
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// Main entry point for the semantic analysis phase.
pub fn lower<'ctx>(ast: Ast, ctx: &mut Context<'ctx>) -> std::result::Result<Mir, ErrorBuf> {
    MirBuilder::new(&ast, ctx).lower()
}

/// This struct handles lowering from the Ast to the Mir.
pub struct MirBuilder<'mir, 'ctx> {
    ast: &'mir Ast,
    /// The context must be mutable to add types to its interner. If type
    /// checking and inference becomes a separate, earlier phase, this will no
    /// longer be necessary.
    ctx: &'mir mut Context<'ctx>,
    mir: Mir,
    pub errors: ErrorBuf,
}

impl<'mir, 'ctx> MirBuilder<'mir, 'ctx> {
    pub fn new(ast: &'mir Ast, ctx: &'mir mut Context<'ctx>) -> Self {
        let mir = Mir::new(&ast);
        Self {
            ast,
            ctx,
            mir,
            errors: ErrorBuf::new(),
        }
    }

    /// Typecheck all functions in the AST, enter the lowered functions in the cfg
    pub fn lower(mut self) -> std::result::Result<Mir, ErrorBuf> {
        for (id, func) in self.ast.funcs.iter().enumerate() {
            // TODO a better way to do this
            let fn_id = FnId::new(id as u32);

            let body = &self.ast.bodies[func.body];
            let sig = match self.type_sig(&func.sig, &func.table) {
                Ok(sig) => sig,
                _ => {
                    continue;
                }
            };
            // The table argument serves to pass in the function's environment.
            let builder = GraphBuilder::new(self.ctx, body, &sig, func.table);
            let graph = match builder.lower() {
                Ok(gr) => gr,
                Err(mut errs) => {
                    self.errors.append(&mut errs);
                    continue;
                }
            };

            self.mir.graphs.insert(fn_id, graph);
        }

        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            Ok(self.mir)
        }
    }

    /// Resolve the types in a function signature
    pub fn type_sig(&mut self, sig: &Sig, tab: &TableId) -> Result<TypedSig> {
        let params = sig
            .params
            .iter()
            .map(|p| typecheck::resolve_type(&mut self.ctx, &p.ty, tab))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let output = match &sig.output {
            None => self.ctx.types.intern(Type::unit()),
            Some(annot) => typecheck::resolve_type(&mut self.ctx, annot, tab)?,
        };
        let sig = TypedSig { params, output };
        Ok(sig)
    }
}

// ====== Graph building ======

/// A helper struct for tracking the reified referents (as `LocalId`s) of
/// symbols. It's just a vector of maps, with a pointer to the currently active
/// one. This should be a little less expensive than a linked list, since we
/// need only clear a table and move back the cursor to pop a table.
///
/// Note: nobody is stopping you from trying to pop beyond the first table. such
/// underflow would be a bug; therefore you must be careful always to call
/// `push_table` and `pop_table` in pairs.
struct SymbolTable {
    tables: Vec<HashMap<SymbolId, LocalId>>,
    current: usize,
}

impl SymbolTable {
    fn new() -> Self {
        Self {
            tables: vec![HashMap::new()],
            current: 0,
        }
    }

    fn push_table(&mut self) {
        if self.current == self.tables.len() - 1 {
            self.tables.push(HashMap::new());
        }
        self.current += 1;
    }

    fn pop_table(&mut self) {
        // NOTE: if you're clever, you won't even have to clear this.
        self.tables[self.current].clear();
        self.current -= 1;
    }

    /// NOTE: this is actually incorrect, because of how it should interact with function scope.
    fn get(&self, item: &SymbolId) -> Option<&LocalId> {
        let mut cursor = self.current;
        loop {
            if let local @ Some(_) = self.tables[cursor].get(&item) {
                return local;
            } else {
                if cursor > 0 {
                    cursor -= 1;
                } else {
                    return None;
                }
            }
        }
    }

    /// Always insert in the top table
    fn insert(&mut self, k: SymbolId, v: LocalId) -> Option<LocalId> {
        self.tables[self.current].insert(k, v)
    }
}

pub struct GraphBuilder<'mir, 'ctx> {
    /// The context must be mutable to add types to its interner. If type
    /// checking and inference becomes a separate, earlier phase, this will no
    /// longer be necessary.
    ctx: &'mir mut Context<'ctx>,
    /// The AST body of this function
    body: &'mir Expr,
    /// The MIR representation of this function
    gr: Graph,
    /// A stack of locals tables
    st: SymbolTable,
    /// The currently active items table
    table: TableId,
    /// The currently active basic block
    cursor: BlockId,
    /// This function's signature
    sig: &'mir TypedSig,
    pub errors: ErrorBuf,
}

impl<'mir, 'ctx> GraphBuilder<'mir, 'ctx> {
    pub fn new(
        ctx: &'mir mut Context<'ctx>,
        body: &'mir Expr,
        sig: &'mir TypedSig,
        table: TableId,
    ) -> Self {
        let TypedSig { params, output } = sig;

        let mut gr = Graph::new();
        let cursor = gr.entry_block;

        gr.locals.insert(Local {
            ty: *output,
            kind: LocalKind::User,
        });

        for param in params {
            gr.locals.insert(Local {
                ty: *param,
                kind: LocalKind::User,
            });
        }

        Self {
            ctx,
            body,
            gr,
            st: SymbolTable::new(),
            table,
            cursor,
            sig,
            errors: ErrorBuf::new(),
        }
    }

    #[inline]
    pub fn push_stmt(&mut self, stmt: mir::Stmt) {
        self.gr.push_stmt(self.cursor, stmt);
    }

    pub fn lower(mut self) -> std::result::Result<Graph, ErrorBuf> {
        let place = self.gr.return_site();
        let _ = self.lower_into(place, self.body);

        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            Ok(self.gr)
        }
    }

    #[allow(unused_variables)]
    pub fn lower_into(&mut self, place: LocalId, expr: &Expr) -> Result<()> {
        match &expr.data {
            ExprKind::BinOp { left, op, right } => self.lower_into_binop(place, left, op, right),
            ExprKind::UnOp { op, right } => self.lower_into_unop(place, op, right),
            ExprKind::Literal(lit) => self.lower_into_literal(place, lit),
            ExprKind::Ident(ident) => self.lower_into_ident(place, ident),
            ExprKind::Tuple(_) => {
                todo!()
            }
            ExprKind::IntArr { item, reps } => {
                todo!()
            }
            ExprKind::ExtArr(_) => {
                todo!()
            }
            ExprKind::Block(block) => self.lower_into_block(place, block),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                todo!()
            }
            ExprKind::For { bind, iter, body } => {
                todo!()
            }
            ExprKind::Call { callee, args } => {
                todo!()
            }
            ExprKind::Index { head, index } => {
                todo!()
            }
        }
    }

    fn lower_into_binop(
        &mut self,
        place: LocalId,
        left: &Expr,
        op: &ast::BinOp,
        right: &Expr,
    ) -> Result<()> {
        let ty = self.gr.locals[place].ty;
        // Let's assume for now that all the binops take the same two types, in
        // both arguments. This won't be true, but it's a convenient simplifying
        // assumption.
        let l_place = self.gr.auto_local(ty);
        let r_place = self.gr.auto_local(ty);

        let left = self.lower_into(l_place, left);
        let right = self.lower_into(r_place, right);
        if let (Err(e), _) | (_, Err(e)) = (left, right) {
            return Err(e);
        }

        // FIXME for now, pretend that all operations are `Copy`.
        let l_op = Operand::Copy(l_place);
        let r_op = Operand::Copy(r_place);
        let rhs = Rvalue::BinOp(op.data, l_op, r_op);
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_unop(&mut self, place: LocalId, op: &ast::UnOp, right: &Expr) -> Result<()> {
        // NOTE this is explicitly incorrect
        let ty = self.gr.locals[place].ty;
        let r_place = self.gr.auto_local(ty);
        self.lower_into(r_place, right)?;

        // FIXME for now, pretend that all operations are `Copy`.
        let r_op = Operand::Copy(r_place);
        let rhs = Rvalue::UnOp(op.data, r_op);
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_literal(&mut self, place: LocalId, lit: &Literal) -> Result<()> {
        let constant = match &lit.data {
            LiteralKind::True => Const::True,
            LiteralKind::False => Const::False,
            LiteralKind::Nat(n) => Const::Nat(*n),
        };
        let rhs = Rvalue::Const(constant);
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_ident(&mut self, _place: LocalId, _ident: &Ident) -> Result<()> {
        Ok(())
    }

    fn lower_into_block(&mut self, place: LocalId, block: &Block) -> Result<()> {
        #![allow(unused_variables)]
        let Block {
            stmts,
            expr,
            table,
            span,
        } = block;

        for stmt in stmts.iter() {
            self.lower_stmt(stmt)?;
        }

        match expr {
            Some(expr) => self.lower_into(place, expr),
            None => {
                // todo!();
                Ok(())
            }
        }
    }

    #[allow(unused_variables)]
    fn lower_stmt(&mut self, stmt: &ast::Stmt) -> Result<()> {
        match &stmt.data {
            StmtKind::Print(_) => {
                todo!()
            }
            StmtKind::Expr(expr) | StmtKind::ExprSemi(expr) => {
                todo!()
            }
            StmtKind::Local { lhs, ty, rhs } => {
                let ty = ty.as_ref().unwrap(); // For now, crash without annotation
                let ty = typecheck::resolve_type(&mut self.ctx, ty, &self.table)?;
                let place = self.gr.user_local(ty);
                self.st.insert(lhs.data, place);
                if let Some(rhs) = rhs {
                    self.lower_into(place, rhs)?;
                }
                Ok(())
            }
            StmtKind::Item(_) => {
                todo!()
            }
        }
    }
}

/// This module provides some helper functions for resolving type annotations,
/// and might contain a little bit of ad-hoc type inference logic. Should we
/// ever add real type inference, it will be broken out into another file or
/// even a separate crate.
mod typecheck {
    use super::*;
    /// Resolve an annotation to a type, given a table (scope) in which it
    /// should appear. This should eventually be farmed out to a type inference
    /// module/crate, and/or appear earlier in the compilaton process. For now it doesn't hurt to include here.
    pub fn resolve_type<'a>(ctx: &mut Context<'a>, annot: &Annot, tab: &TableId) -> Result<TyId> {
        let ty = match &annot.data {
            AnnotKind::Bool => {
                let ty = Type::Bool;
                ctx.types.intern(ty)
            }
            AnnotKind::Uint(u) => {
                let ty = Type::Uint(*u);
                ctx.types.intern(ty)
            }
            AnnotKind::Tuple(inners) => {
                let inner_types = inners
                    .iter()
                    .map(|ann| resolve_type(ctx, ann, tab))
                    .collect::<Result<Vec<TyId>>>()?;
                ctx.types.intern(Type::Tuple(inner_types))
            }
            AnnotKind::Array(inner) => {
                let inner = resolve_type(ctx, inner, tab)?;
                ctx.types.intern(Type::Array(inner))
            }
            AnnotKind::Question(inner) => {
                let ty = resolve_type(ctx, inner, tab)?;
                resolve_annot_question(ctx, ty)?
            }
            AnnotKind::Bang(inner) => {
                let ty = resolve_type(ctx, inner, tab)?;
                resolve_annot_bang(ctx, ty)?
            }
            AnnotKind::Ident(_ident) => {
                todo!()
            }
        };

        Ok(ty)
    }

    fn resolve_annot_question<'a>(ctx: &mut Context<'a>, inner: TyId) -> Result<TyId> {
        use Type::*;
        // can this be done with just pointer comparisons?
        let ty = match ctx.types[inner] {
            Bool => Q_Bool,
            Uint(u) => Q_Uint(u),
            _ => unimplemented!(),
        };
        Ok(ctx.types.intern(ty))
    }

    fn resolve_annot_bang(ctx: &mut Context, inner: TyId) -> Result<TyId> {
        use Type::*;
        // can this be done with just pointer comparisons?
        let ty = match ctx.types[inner] {
            Q_Bool => Bool,
            Q_Uint(u) => Uint(u),
            _ => unimplemented!(),
        };
        Ok(ctx.types.intern(ty))
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
        #[msg = "operator `{kind}` doesn't support argument type `{right}`"]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual right operand type
        pub right: Type,
    }

    #[derive(Diagnostic)]
    pub struct DestructuringError {
        #[msg = "pattern fails to match type `{actual}`"]
        pub span: Span,
        /// The type
        pub actual: Type,
    }

    #[derive(Diagnostic)]
    pub struct NameCollision {
        #[msg = "name `{name}` was previously bound"]
        pub span: Span,
        pub name: String,
    }

    #[derive(Diagnostic)]
    pub struct HeterogeneousArray {
        #[msg = "element's type differs from `{ty}`"]
        pub span: Span,
        pub ty: Type,
    }

    #[derive(Diagnostic)]
    pub struct ExpectedSizeType {
        #[msg = "expected size type, found `{ty}`"]
        pub span: Span,
        pub ty: Type,
    }

    #[derive(Diagnostic)]
    pub struct UnboundName {
        #[msg = "name `{name}` is not bound"]
        pub span: Span,
        pub name: String,
    }
}
