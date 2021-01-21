use crate::cavy_errors::{CavyError, Diagnostic, ErrorBuf, Maybe};
use crate::{
    ast::{self, *},
    source::Span,
};
// use crate::functions::{Func, UserFunc};
use crate::context::{Context, SymbolId};
use crate::{
    mir::{self, *},
    store::Index,
    types::{TyId, Type},
};
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// Main entry point for the semantic analysis phase.
pub fn lower<'ctx>(ast: Ast, ctx: &mut Context<'ctx>) -> Result<Mir, ErrorBuf> {
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
    pub fn lower(mut self) -> Result<Mir, ErrorBuf> {
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
    pub fn type_sig(&mut self, sig: &Sig, tab: &TableId) -> Maybe<TypedSig> {
        let params = sig
            .params
            .iter()
            .map(|p| {
                let ty = typecheck::resolve_type(&p.ty, tab, &mut self.ctx);
                Ok((p.name.data, ty?))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output = match &sig.output {
            None => self.ctx.types.intern(Type::unit()),
            Some(annot) => typecheck::resolve_type(annot, tab, &mut self.ctx)?,
        };
        let sig = TypedSig {
            params,
            output,
            span: sig.span,
        };
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
        let TypedSig { params, output, .. } = sig;

        let mut gr = Graph::new();
        let mut st = SymbolTable::new();
        let cursor = gr.entry_block;

        gr.locals.insert(Local {
            ty: *output,
            kind: LocalKind::User,
        });

        for (param, ty) in params {
            let local = gr.locals.insert(Local {
                ty: *ty,
                kind: LocalKind::User,
            });
            st.insert(*param, local);
        }

        Self {
            ctx,
            body,
            gr,
            st,
            table,
            cursor,
            sig,
            errors: ErrorBuf::new(),
        }
    }

    fn error<T: 'static + Diagnostic>(&mut self, err: T) -> Maybe<()> {
        Err(self.errors.push(err))
    }

    fn expect_type(&mut self, expected: TyId, actual: TyId, span: Span) -> Maybe<()> {
        if actual != expected {
            self.error(errors::ExpectedType {
                span,
                expected,
                actual,
            })?
        }
        Ok(())
    }

    // === Block-manipulating methods ===

    pub fn push_stmt(&mut self, stmt: mir::Stmt) {
        self.gr.push_stmt(self.cursor, stmt);
    }

    pub fn new_block(&mut self) -> BlockId {
        self.gr.new_block()
    }

    pub fn set_terminator(&mut self, kind: BlockKind) {
        self.gr.blocks[self.cursor].kind = kind;
    }

    /// Temporarily work within the environment of a new goto block
    fn with_goto<T, F>(&mut self, block: BlockId, f: F) -> Maybe<T>
    where
        F: FnOnce(&mut Self) -> Maybe<T>,
    {
        let old_block = self.cursor;
        self.cursor = self.gr.goto_block(block);
        f(self).and_then(|v| {
            self.cursor = old_block;
            Ok(v)
        })
    }

    // === Lowering methods ===

    pub fn lower(mut self) -> Result<Graph, ErrorBuf> {
        let place = self.gr.return_site();
        let _ = self.lower_into(place, self.body);

        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            Ok(self.gr)
        }
    }

    #[allow(unused_variables)]
    pub fn lower_into(&mut self, place: LocalId, expr: &Expr) -> Maybe<()> {
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
            ExprKind::If { cond, dir, ind } => self.lower_into_if(place, cond, dir, ind),
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
    ) -> Maybe<()> {
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

        let l_op = Operand::Place(l_place);
        let r_op = Operand::Place(r_place);
        let rhs = Rvalue::BinOp(op.data, l_op, r_op);
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_unop(&mut self, place: LocalId, op: &ast::UnOp, right: &Expr) -> Maybe<()> {
        // NOTE this is explicitly incorrect
        let ty = self.gr.locals[place].ty;
        // Should not be here, of course
        let r_place = self.gr.auto_local(ty);
        self.lower_into(r_place, right)?;

        let r_op = Operand::Place(r_place);
        let rhs = Rvalue::UnOp(op.data, r_op);
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_literal(&mut self, place: LocalId, lit: &Literal) -> Maybe<()> {
        let ty = self.gr.locals[place].ty;
        let constant = match &lit.data {
            LiteralKind::True => {
                self.expect_type(ty, self.ctx.common.bool, lit.span)?;
                Const::True
            }
            LiteralKind::False => {
                self.expect_type(ty, self.ctx.common.bool, lit.span)?;
                Const::False
            }
            LiteralKind::Nat(n) => {
                if ty != self.ctx.common.u4
                    && ty != self.ctx.common.u8
                    && ty != self.ctx.common.u16
                    && ty != self.ctx.common.u32
                {
                    self.error(errors::ExpectedType {
                        span: lit.span,
                        expected: ty,
                        actual: self.ctx.common.u32,
                    })?;
                }
                Const::Nat(*n)
            }
        };
        let rhs = Rvalue::Const(constant);
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_ident(&mut self, place: LocalId, ident: &Ident) -> Maybe<()> {
        let rhs = match self.st.get(&ident.data) {
            // FIXME for now, pretend that all operations are `Copy`.
            Some(local) => Rvalue::Copy(*local),
            None => {
                return self.error(errors::UnboundName {
                    span: ident.span,
                    name: ident.data,
                });
            }
        };
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    /// Lower an AST block and store its value in the given location.
    fn lower_into_block(&mut self, place: LocalId, block: &Block) -> Maybe<()> {
        #![allow(unused_variables)]
        let Block {
            stmts,
            expr,
            table,
            span,
        } = block;

        let (_, errors): (Vec<_>, Vec<_>) = stmts
            .iter()
            .map(|stmt| self.lower_stmt(stmt))
            .partition(Maybe::is_ok);
        if let Some(err) = errors.into_iter().next() {
            err?;
        }

        match expr {
            Some(expr) => self.lower_into(place, expr),
            None => Ok(()),
        }
    }

    fn lower_into_if(
        &mut self,
        place: LocalId,
        cond: &Expr,
        dir: &Block,
        ind: &Option<Box<Block>>,
    ) -> Maybe<()> {
        // TODO: `lower_into`, and all the `lower_into_` functions, should
        // return a `Result<LocalId>`, where on success they echo back the
        // location they were lowered into. It would make this all a lot neater.
        // Could expect to get Ok(cond), then unwrap in the same match as `dir`
        // and `ind`.
        //
        // TODO: Again, I'm cheating by trying to fit this into a
        // `bool`, when it could also be a `?bool`.
        let cond_ty = match self.infer_type(cond) {
            Some(ty) => ty,
            None => {
                return self.error(errors::InferenceFailure { span: cond.span });
            }
        };
        let cond_place = self.gr.auto_local(cond_ty);
        let cond = self.lower_into(cond_place, cond);
        let tail_block = self.new_block();

        // Direct branch
        let dir = self.with_goto(tail_block, |this| {
            this.lower_into_block(place, dir)?;
            Ok(this.cursor)
        });

        // Indirect branch
        let ind = match ind {
            Some(ind) => self.with_goto(tail_block, |this| {
                this.lower_into_block(place, ind)?;
                Ok(this.cursor)
            }),
            None => Ok(tail_block),
        };

        let (dir, ind, _) = match (dir, ind, cond) {
            (Ok(dir), Ok(ind), Ok(cond)) => Ok((dir, ind, cond)),
            (Err(err), _, _) | (_, Err(err), _) | (_, _, Err(err)) => Err(err),
        }?;

        let switch = BlockKind::Switch {
            cond: cond_place,
            blks: vec![dir, ind],
        };
        self.set_terminator(switch);
        self.cursor = tail_block;
        Ok(())
    }

    #[allow(unused_variables)]
    fn lower_stmt(&mut self, stmt: &ast::Stmt) -> Maybe<()> {
        match &stmt.data {
            StmtKind::Print(_) => {
                todo!()
            }
            StmtKind::Expr(expr) | StmtKind::ExprSemi(expr) => {
                // ...Make something up, for now? But in fact, you'll have to do
                // some kind of "weak"/"ad hoc" type inference to get this type.
                let ty = self.ctx.types.intern(Type::unit());
                let place = self.gr.auto_local(ty);
                self.lower_into(place, expr)
            }
            StmtKind::Local { lhs, ty, rhs } => {
                // Is this annotated, or must we infer the type?
                let ty = match (ty, rhs) {
                    // This should work if we ever have proper type inferece; in
                    // the *near* future it should emit an error message, but for now let's just fail.
                    (None, None) => unimplemented!(),
                    (Some(ty), _) => typecheck::resolve_type(ty, &self.table, self.ctx)?,
                    (_, Some(rhs)) => match self.infer_type(rhs) {
                        Some(ty) => ty,
                        None => return self.error(errors::InferenceFailure { span: rhs.span }),
                    },
                };
                let place = self.gr.user_local(ty);
                self.st.insert(lhs.data, place);
                if let Some(rhs) = rhs {
                    self.lower_into(place, rhs)?;
                }
                Ok(())
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

    /// These should all be very small, simple types. We have nothing fancy: no
    /// generics, just a few numeric types, and so on.
    pub type TySet = Vec<TyId>;

    fn intersect(fst: &mut TySet, snd: &TySet) {
        let mut snd = snd.iter();
        let r = snd.next();
        fst.retain(|l| match r {
            None => false,
            Some(r) => match l.cmp(r) {
                std::cmp::Ordering::Greater => {
                    while let Some(r) = snd.next() {
                        if r == l {
                            return true;
                        }
                        if r > l {
                            break;
                        }
                    }
                    r == l
                }
                std::cmp::Ordering::Equal => true,
                std::cmp::Ordering::Less => false,
            },
        })
    }

    #[cfg(test)]
    #[test]
    fn intersect_simple() {
        let mut v1 = vec![TyId::new(1), TyId::new(2), TyId::new(3)];
        let v2 = vec![TyId::new(2), TyId::new(3), TyId::new(4)];
        let expect = vec![TyId::new(2), TyId::new(3)];
        intersect(&mut v1, &v2);
        assert_eq!(v1, expect);
    }

    /// We're not doing full type inference, but we do need to know what to do
    /// when we call a function and ignore its return value. Or, when we move a
    /// variable into a new binding that doesn't have an annotation. These
    /// methods provide the "ad hoc," weak type inference needed to lower such
    /// expressions. Note that we're spreading out type checking and inference
    /// across this file, so it might be ugly to clean up later.
    ///
    /// Also note that all this is a horribly inefficient stopgap.
    impl<'mir, 'ctx> GraphBuilder<'mir, 'ctx> {
        pub fn infer_type<'a>(&self, expr: &Expr) -> Option<TyId> {
            let tys = self.infer_type_inner(expr);
            // This is very naive and silly, but I just want to get *some* element,
            // if there is one.
            tys.last().map(|t| *t)
        }

        #[allow(unused_variables)]
        pub fn infer_type_inner(&self, expr: &Expr) -> TySet {
            match &expr.data {
                ExprKind::BinOp { left, op, right } => self.infer_binop(left, op, right),
                ExprKind::UnOp { op, right } => self.infer_unop(op, right),
                ExprKind::Literal(lit) => self.infer_literal(lit),
                ExprKind::Ident(ident) => self.infer_ident(ident),
                ExprKind::Tuple(_) => todo!(),
                ExprKind::IntArr { item, reps } => todo!(),
                ExprKind::ExtArr(_) => todo!(),
                ExprKind::Block(block) => self.infer_block(block),
                ExprKind::If { cond, dir, ind } => {
                    let mut dir = self.infer_block(dir);
                    let ind = ind
                        .as_ref()
                        .map_or(vec![self.ctx.common.unit], |b| self.infer_block(&b));
                    intersect(&mut dir, &ind);
                    dir
                }
                ExprKind::For { bind, iter, body } => {
                    // should be the unit type
                    vec![self.ctx.common.unit]
                }
                ExprKind::Call { callee, args } => todo!(),
                ExprKind::Index { head, index } => todo!(),
            }
        }

        fn infer_binop(&self, left: &Expr, op: &ast::BinOp, right: &Expr) -> TySet {
            // let set = TySet::new();
            // set

            let mut left = self.infer_type_inner(left);
            let right = self.infer_type_inner(right);

            match &op.data {
                BinOpKind::Equal => vec![self.ctx.common.bool, self.ctx.common.q_bool],
                BinOpKind::Nequal => vec![self.ctx.common.bool, self.ctx.common.q_bool],
                BinOpKind::DotDot => todo!(),
                BinOpKind::Plus => {
                    intersect(&mut left, &right);
                    left
                }
                BinOpKind::Minus => todo!(),
                BinOpKind::Times => {
                    intersect(&mut left, &right);
                    left
                }
                BinOpKind::Mod => todo!(),
                BinOpKind::Less => todo!(),
                BinOpKind::Greater => todo!(),
            }
        }

        fn infer_unop(&self, op: &ast::UnOp, right: &Expr) -> TySet {
            let right = self.infer_type_inner(right);
            match &op.data {
                UnOpKind::Minus => todo!(),
                UnOpKind::Not => right,
                UnOpKind::Linear => {
                    let mut tys = TySet::new();
                    for ty in right {
                        if ty == self.ctx.common.bool {
                            tys.push(self.ctx.common.q_bool)
                        } else if ty == self.ctx.common.u4 {
                            tys.push(self.ctx.common.q_u4)
                        } else if ty == self.ctx.common.u8 {
                            tys.push(self.ctx.common.q_u8)
                        } else if ty == self.ctx.common.u16 {
                            tys.push(self.ctx.common.q_u16)
                        } else if ty == self.ctx.common.u32 {
                            tys.push(self.ctx.common.q_u32)
                        }
                    }
                    tys.sort();
                    tys
                }
                UnOpKind::Delin => {
                    let mut tys = TySet::new();
                    for ty in right {
                        if ty == self.ctx.common.q_bool {
                            tys.push(self.ctx.common.bool)
                        } else if ty == self.ctx.common.q_u4 {
                            tys.push(self.ctx.common.u4)
                        } else if ty == self.ctx.common.q_u8 {
                            tys.push(self.ctx.common.u8)
                        } else if ty == self.ctx.common.q_u16 {
                            tys.push(self.ctx.common.u16)
                        } else if ty == self.ctx.common.q_u32 {
                            tys.push(self.ctx.common.u32)
                        }
                    }
                    tys.sort();
                    tys
                }
            }
        }

        fn infer_literal(&self, lit: &Literal) -> TySet {
            let mut tys = match &lit.data {
                LiteralKind::True => vec![self.ctx.common.bool],
                LiteralKind::False => vec![self.ctx.common.bool],
                LiteralKind::Nat(_) => {
                    vec![
                        self.ctx.common.u4,
                        self.ctx.common.u8,
                        self.ctx.common.u16,
                        self.ctx.common.u32,
                    ]
                }
            };
            tys.sort();
            tys
        }

        fn infer_block(&self, block: &Block) -> TySet {
            match &block.expr {
                Some(expr) => self.infer_type_inner(expr),
                None => vec![self.ctx.common.unit],
            }
        }

        fn infer_ident(&self, ident: &Ident) -> TySet {
            let mut set = TySet::new();
            if let Some(local) = self.st.get(&ident.data) {
                set.push(self.gr.locals[*local].ty)
            }

            set
        }
    }

    /// Resolve an annotation to a type, given a table (scope) in which it
    /// should appear. This should eventually be farmed out to a type inference
    /// module/crate, and/or appear earlier in the compilaton process. For now it doesn't hurt to include here.
    pub fn resolve_type<'a>(annot: &Annot, tab: &TableId, ctx: &mut Context<'a>) -> Maybe<TyId> {
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
                    .map(|ann| resolve_type(ann, tab, ctx))
                    .collect::<Maybe<Vec<TyId>>>()?;
                ctx.types.intern(Type::Tuple(inner_types))
            }
            AnnotKind::Array(inner) => {
                let inner = resolve_type(inner, tab, ctx)?;
                ctx.types.intern(Type::Array(inner))
            }
            AnnotKind::Question(inner) => {
                let ty = resolve_type(inner, tab, ctx)?;
                resolve_annot_question(ctx, ty)?
            }
            AnnotKind::Bang(inner) => {
                let ty = resolve_type(inner, tab, ctx)?;
                resolve_annot_bang(ctx, ty)?
            }
            AnnotKind::Ident(_ident) => {
                todo!()
            }
        };

        Ok(ty)
    }

    fn resolve_annot_question<'a>(ctx: &mut Context<'a>, inner: TyId) -> Maybe<TyId> {
        use Type::*;
        // can this be done with just pointer comparisons?
        let ty = match ctx.types[inner] {
            Bool => Q_Bool,
            Uint(u) => Q_Uint(u),
            _ => unimplemented!(),
        };
        Ok(ctx.types.intern(ty))
    }

    fn resolve_annot_bang(ctx: &mut Context, inner: TyId) -> Maybe<TyId> {
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
    use crate::context::SymbolId;
    use crate::source::Span;
    use crate::types::TyId;
    use cavy_macros::Diagnostic;

    // This will be a stand-in catch-all error for when a specific type is
    // expected and not found.
    #[derive(Diagnostic)]
    pub struct ExpectedType {
        #[msg = "expected type `{expected}`, found `{actual}`"]
        pub span: Span,
        #[ctx]
        pub expected: TyId,
        #[ctx]
        pub actual: TyId,
    }

    /// TODO This error should go in a type inference model when the day comes
    /// that we add HM type inference to the language.
    #[derive(Diagnostic)]
    pub struct InferenceFailure {
        #[msg = "could not infer a type for expression"]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    pub struct BinOpTypeError {
        #[msg = "operator `{kind}` doesn't support argument types `{left}` and `{right}`"]
        pub span: Span,
        /// The operator
        pub kind: BinOpKind,
        /// The actual left operand type
        #[ctx]
        pub left: TyId,
        /// The actual right operand type
        #[ctx]
        pub right: TyId,
    }

    #[derive(Diagnostic)]
    pub struct UnOpTypeError {
        #[msg = "operator `{kind}` doesn't support argument type `{right}`"]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual right operand type
        #[ctx]
        pub right: TyId,
    }

    #[derive(Diagnostic)]
    pub struct DestructuringError {
        #[msg = "pattern fails to match type `{actual}`"]
        pub span: Span,
        /// The type
        #[ctx]
        pub actual: TyId,
    }

    #[derive(Diagnostic)]
    pub struct HeterogeneousArray {
        #[msg = "element's type differs from `{ty}`"]
        pub span: Span,
        #[ctx]
        pub ty: TyId,
    }

    #[derive(Diagnostic)]
    pub struct ExpectedSizeType {
        #[msg = "expected size type, found `{ty}`"]
        pub span: Span,
        #[ctx]
        pub ty: TyId,
    }

    #[derive(Diagnostic)]
    pub struct UnboundName {
        #[msg = "name `{name}` is not bound"]
        pub span: Span,
        #[ctx]
        pub name: SymbolId,
    }
}
