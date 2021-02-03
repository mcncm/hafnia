use crate::{
    ast::{self, *},
    source::Span,
};
use crate::{
    cavy_errors::{CavyError, Diagnostic, ErrorBuf, Maybe},
    num::Uint,
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
                let ty = typing::resolve_type(&p.ty, tab, &mut self.ctx);
                Ok((p.name.data, ty?))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output = match &sig.output {
            None => self.ctx.types.intern(Type::unit()),
            Some(annot) => typing::resolve_type(annot, tab, &mut self.ctx)?,
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
/// Note: nobody is stopping you from trying to pop beyond the first table. Such
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
    /// A "typing context" of types assigned to each expression node
    gamma: HashMap<NodeId, TyId>,
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
            gamma: HashMap::new(),
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
        let ty = self.type_expr(expr)?;
        // This is now the center of all type-checking
        self.expect_type(self.gr.locals[place].ty, ty, expr.span)?;
        match &expr.data {
            ExprKind::BinOp { left, op, right } => {
                self.lower_into_binop(place, left, op, right, &expr.span)
            }
            ExprKind::UnOp { op, right } => self.lower_into_unop(place, op, right, &expr.span),
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
        span: &Span,
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

        let stmt = mir::Stmt {
            place,
            rhs: Rvalue {
                span: *span,
                data: RvalueKind::BinOp(op.data, l_place, r_place),
            },
        };
        self.push_stmt(stmt);
        Ok(())
    }

    fn lower_into_unop(
        &mut self,
        place: LocalId,
        op: &ast::UnOp,
        right: &Expr,
        span: &Span,
    ) -> Maybe<()> {
        // Should not be here, of course
        let arg_ty = self.gamma.get(&right.node).unwrap();
        let r_place = self.gr.auto_local(*arg_ty);
        self.lower_into(r_place, right)?;

        let rhs = Rvalue {
            span: *span,
            data: RvalueKind::UnOp(op.data, r_place),
        };
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
            LiteralKind::Nat(n, sz) => {
                let lit_ty = match sz {
                    Some(Uint::U2) => todo!(),
                    Some(Uint::U4) => self.ctx.common.u4,
                    Some(Uint::U8) => self.ctx.common.u8,
                    Some(Uint::U16) => self.ctx.common.u16,
                    Some(Uint::U32) => self.ctx.common.u32,
                    None => self.ctx.common.u32,
                };
                self.expect_type(ty, lit_ty, lit.span)?;
                Const::Nat(*n)
            }
        };
        let rhs = Rvalue {
            span: lit.span,
            data: RvalueKind::Const(constant),
        };
        self.push_stmt(mir::Stmt { place, rhs });
        Ok(())
    }

    fn lower_into_ident(&mut self, place: LocalId, ident: &Ident) -> Maybe<()> {
        let rhs = match self.st.get(&ident.data) {
            Some(id) => {
                let local = &self.gr.locals[*id];
                if local.ty.is_linear(self.ctx) {
                    Rvalue {
                        span: ident.span,
                        data: RvalueKind::Move(*id),
                    }
                } else {
                    Rvalue {
                        span: ident.span,
                        data: RvalueKind::Copy(*id),
                    }
                }
            }
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
        let cond_ty = self.type_expr(cond)?;
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
                    (Some(ty), _) => typing::resolve_type(ty, &self.table, self.ctx)?,
                    (_, Some(rhs)) => self.type_inner(rhs)?,
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

mod typing {
    //! This module provides some helper functions for resolving type
    //! annotations, and might contain a little bit of ad-hoc type inference
    //! logic. The type inference supported here is supposed to be minimal, as
    //! it's not the main focus of this language. Should we ever add "real"
    //! Hindley-Milner type inference, it will be broken out into another file
    //! or even a separate crate.
    use super::*;
    use crate::{index_type, store::Counter};

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

    index_type! { TyVarId }

    #[derive(Debug, Clone, Copy)]
    pub struct TyVar {
        /// Is this type constrained to be linear or not?
        lin: Option<bool>,
        kind: TyVarKind,
    }

    #[derive(Debug, Clone, Copy)]
    pub enum TyVarKind {
        /// An unrestricted type variable
        Var(TyVarId),
        /// A type variable that must be an integer type (e.g. `u8`, `?u8`, ...)
        // I guess we'll give this class of type variables the option of being
        // linear or nonlinear. We can then assert equality of a linear one with
        // a nonlinear one. These can be appropriately unified, since they
        // always come in pairs.
        Int(TyVarId),
        /// A `bool` or `?bool`
        Boolean(TyVarId),
    }

    /// An inference type: either a concrete type or a type variable.
    #[derive(Debug, Clone, Copy)]
    pub enum InfTy {
        TyId(TyId),
        TyVar(TyVar),
    }

    /// A type constraint, or type equation, in which the left- and right- hand
    /// inference types are asserted equal.
    #[derive(Debug)]
    pub struct TyConstr(InfTy, InfTy);

    /// An inference context in which to solve types.
    struct InfCtx<'a, 'ctx> {
        /// The *single expression* whose type we're trying to solve
        root: &'a Expr,
        /// The items table from the AST
        tab: &'a ast::Table,
        /// The calling graph builder
        builder: &'a GraphBuilder<'a, 'ctx>,
        /// A counter for type variables
        ctr: Counter<TyVarId>,
        /// A typing context mapping expressions to the inference type currently
        /// held for them.
        gamma: HashMap<NodeId, InfTy>,
        /// The currently-active type constraints
        constrs: Vec<TyConstr>,
    }

    impl<'a, 'ctx> InfCtx<'a, 'ctx> {
        fn new(expr: &'a Expr, tab: &'a Table, builder: &'a GraphBuilder<'a, 'ctx>) -> Self {
            InfCtx {
                root: expr,
                tab,
                builder,
                ctr: Counter::new(),
                gamma: HashMap::new(),
                constrs: Vec::new(),
            }
        }

        // fn unify_constr(&mut self, constr: &TyConstr) {
        //     let TyConstr(left, right) = constr;
        //     match (left, right) {
        //         (InfTy::TyId(idl), InfTy::TyId(idr)) => {}
        //         (InfTy::TyId(id), InfTy::TyVar(var)) | (InfTy::TyVar(var), InfTy::TyId(id)) => {}
        //         (InfTy::TyVar(varl), InfTy::TyVar(varr)) => {}
        //     }
        // }

        /// Assert a known type for the top-level expression
        fn as_type(mut self, ty: TyId) -> Self {
            self.gamma.insert(self.root.node, InfTy::TyId(ty));
            self
        }

        /// Produce an assignment of all subexpressions
        fn infer(mut self) -> Option<HashMap<&'a Expr, TyId>> {
            self.walk();
            None
            //
        }

        /// Walk the tree, inserting type variables and constraints for each
        /// subexpression. This should probably never fail; we're just naming things.
        fn walk(&mut self) {
            // If we didn't call `as_type`, insert an unconditional type variable at the root.
            // FIXME this is currently incorrect: it will be overwritten.
            if let None = self.gamma.get(&self.root.node) {
                self.gamma.insert(
                    self.root.node,
                    InfTy::TyVar(TyVar {
                        lin: None,
                        kind: TyVarKind::Var(self.ctr.new_index()),
                    }),
                );
            }
            self.walk_inner(self.root);
        }

        #[allow(unused_variables)]
        fn walk_inner(&mut self, expr: &Expr) -> InfTy {
            let node = expr.node;
            match &expr.data {
                ExprKind::BinOp { left, op, right } => self.walk_binop(node, left, op, right),
                ExprKind::UnOp { op, right } => self.walk_unop(node, op, right),
                ExprKind::Literal(lit) => match &lit.data {
                    LiteralKind::True => self.new_boolean(node),
                    LiteralKind::False => self.new_boolean(node),
                    LiteralKind::Nat(_, _) => self.new_int(node, None),
                },
                ExprKind::Ident(ident) => {
                    // NOTE we're not yet inferencing over the whole procedure;
                    // if we see an index, all there is to do is look it up in
                    // the graph.
                    //
                    // This unwrap should be replaced with... something else.
                    let local = self.builder.st.get(&ident.data).unwrap();
                    let local = &self.builder.gr.locals[*local];
                    let ty = InfTy::TyId(local.ty);
                    self.gamma.insert(node, ty);
                    ty
                }
                ExprKind::Tuple(_) => todo!(),
                ExprKind::IntArr { item, reps } => todo!(),
                ExprKind::ExtArr(_) => todo!(),
                ExprKind::Block(_) => todo!(),
                ExprKind::If { cond, dir, ind } => todo!(),
                ExprKind::For { bind, iter, body } => todo!(),
                ExprKind::Call { callee, args } => todo!(),
                ExprKind::Index { head, index } => todo!(),
            }
        }

        #[allow(unused_variables)]
        fn walk_binop(
            &mut self,
            node: NodeId,
            left: &Expr,
            op: &ast::BinOp,
            right: &Expr,
        ) -> InfTy {
            match &op.data {
                BinOpKind::Nequal | BinOpKind::Equal => {
                    let ty = self.new_boolean(node);
                    let left = self.walk_inner(left);
                    let right = self.walk_inner(right);
                    self.new_const(ty, left);
                    self.new_const(ty, right);
                    ty
                }
                BinOpKind::DotDot => todo!(),
                BinOpKind::Plus | BinOpKind::Minus | BinOpKind::Times => {
                    let ty = self.new_int(node, None);
                    let left = self.walk_inner(left);
                    let right = self.walk_inner(right);
                    self.new_const(ty, left);
                    self.new_const(ty, right);
                    ty
                }
                BinOpKind::Mod => todo!(),
                BinOpKind::Less => todo!(),
                BinOpKind::Greater => todo!(),
            }
        }

        #[allow(unused_variables)]
        fn walk_unop(&mut self, node: NodeId, op: &ast::UnOp, right: &Expr) -> InfTy {
            match &op.data {
                UnOpKind::Minus => {
                    let ty = self.new_int(node, None);
                    let right = self.walk_inner(right);
                    self.new_const(ty, right);
                    ty
                }
                UnOpKind::Not => {
                    let ty = self.new_boolean(node);
                    let right = self.walk_inner(right);
                    self.new_const(ty, right);
                    ty
                }
                UnOpKind::Linear => todo!(),
                UnOpKind::Delin => todo!(),
            }
        }

        fn new_const(&mut self, left: InfTy, right: InfTy) {
            self.constrs.push(TyConstr(left, right));
        }

        fn new_boolean(&mut self, node: NodeId) -> InfTy {
            let ty = InfTy::TyVar(TyVar {
                lin: None,
                kind: TyVarKind::Boolean(self.ctr.new_index()),
            });
            self.gamma.insert(node, ty);
            ty
        }

        fn new_var(&mut self, node: NodeId) -> InfTy {
            let ty = InfTy::TyVar(TyVar {
                lin: None,
                kind: TyVarKind::Var(self.ctr.new_index()),
            });
            self.gamma.insert(node, ty);
            ty
        }

        fn new_int(&mut self, node: NodeId, lin: Option<bool>) -> InfTy {
            let ty = InfTy::TyVar(TyVar {
                lin,
                kind: TyVarKind::Int(self.ctr.new_index()),
            });
            self.gamma.insert(node, ty);
            ty
        }
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
        pub fn type_expr<'a>(&mut self, expr: &Expr) -> Maybe<TyId> {
            if let Some(ty) = self.gamma.get(&expr.node) {
                return Ok(*ty);
            }
            self.type_inner(expr)
        }

        #[allow(unused_variables)]
        pub fn type_inner(&mut self, expr: &Expr) -> Maybe<TyId> {
            let ty = match &expr.data {
                ExprKind::BinOp { left, op, right } => self.type_binop(left, op, right)?,
                ExprKind::UnOp { op, right } => self.type_unop(op, right)?,
                ExprKind::Literal(lit) => self.type_literal(lit)?,
                ExprKind::Ident(ident) => self.type_ident(ident)?,
                ExprKind::Tuple(_) => todo!(),
                ExprKind::IntArr { item, reps } => todo!(),
                ExprKind::ExtArr(_) => todo!(),
                ExprKind::Block(block) => self.type_block(block)?,
                ExprKind::If { cond, dir, ind } => todo!(),
                ExprKind::For { bind, iter, body } => {
                    // should be the unit type
                    self.ctx.common.unit
                }
                ExprKind::Call { callee, args } => todo!(),
                ExprKind::Index { head, index } => todo!(),
            };
            self.gamma.insert(expr.node, ty);
            Ok(ty)
        }

        fn type_binop(&mut self, left: &Expr, op: &ast::BinOp, right: &Expr) -> Maybe<TyId> {
            // let set = TySet::new();
            // set

            let left = self.type_inner(left)?;
            let right = self.type_inner(right)?;

            match &op.data {
                BinOpKind::Equal | BinOpKind::Nequal => {
                    if left == right {
                        Ok(left)
                    } else {
                        Err(self.errors.push(errors::BinOpTypeError {
                            span: op.span,
                            kind: op.data,
                            left,
                            right,
                        }))
                    }
                }
                BinOpKind::DotDot => todo!(),
                BinOpKind::Plus | BinOpKind::Times => {
                    if (left == right) & left.is_uint(&self.ctx) {
                        Ok(left)
                    } else {
                        Err(self.errors.push(errors::BinOpTypeError {
                            span: op.span,
                            kind: op.data,
                            left,
                            right,
                        }))
                    }
                }
                BinOpKind::Minus => todo!(),
                BinOpKind::Mod => todo!(),
                BinOpKind::Less => todo!(),
                BinOpKind::Greater => todo!(),
            }
        }

        fn type_unop(&mut self, op: &ast::UnOp, right: &Expr) -> Maybe<TyId> {
            let right = self.type_inner(right)?;
            match &op.data {
                UnOpKind::Minus => todo!(),
                UnOpKind::Not => Ok(right),
                UnOpKind::Linear => {
                    if right == self.ctx.common.bool {
                        Ok(self.ctx.common.q_bool)
                    } else if right == self.ctx.common.u4 {
                        Ok(self.ctx.common.q_u4)
                    } else if right == self.ctx.common.u8 {
                        Ok(self.ctx.common.q_u8)
                    } else if right == self.ctx.common.u16 {
                        Ok(self.ctx.common.q_u16)
                    } else if right == self.ctx.common.u32 {
                        Ok(self.ctx.common.q_u32)
                    } else {
                        Err(self.errors.push(errors::UnOpOutTypeError {
                            span: op.span,
                            kind: op.data,
                            ty: right,
                        }))
                    }
                }
                UnOpKind::Delin => todo!(),
            }
        }

        fn type_literal(&mut self, lit: &Literal) -> Maybe<TyId> {
            let ty = match &lit.data {
                LiteralKind::True => self.ctx.common.bool,
                LiteralKind::False => self.ctx.common.bool,
                LiteralKind::Nat(_, Some(Uint::U2)) => todo!(),
                LiteralKind::Nat(_, Some(Uint::U4)) => self.ctx.common.u4,
                LiteralKind::Nat(_, Some(Uint::U8)) => self.ctx.common.u8,
                LiteralKind::Nat(_, Some(Uint::U16)) => self.ctx.common.u16,
                LiteralKind::Nat(_, Some(Uint::U32)) => self.ctx.common.u32,
                LiteralKind::Nat(_, None) => self.ctx.common.u32,
            };
            Ok(ty)
        }

        fn type_block(&mut self, block: &Block) -> Maybe<TyId> {
            match &block.expr {
                Some(expr) => self.type_inner(expr),
                None => Ok(self.ctx.common.unit),
            }
        }

        fn type_ident(&mut self, ident: &Ident) -> Maybe<TyId> {
            let local = match self.st.get(&ident.data) {
                Some(local) => local,
                None => {
                    return Err(self.errors.push(errors::UnboundName {
                        span: ident.span,
                        name: ident.data,
                    }));
                }
            };
            let local = &self.gr.locals[*local];
            Ok(local.ty)
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
    pub struct UnOpArgTypeError {
        #[msg = "operator `{kind}` doesn't support argument type `{right}`"]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual right operand type
        #[ctx]
        pub right: TyId,
    }

    #[derive(Diagnostic)]
    pub struct UnOpOutTypeError {
        #[msg = "operator `{kind}` doesn't support output type `{ty}`"]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual output type
        #[ctx]
        pub ty: TyId,
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
