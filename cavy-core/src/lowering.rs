use crate::{
    ast::{self, StmtKind, *},
    cavy_errors::{CavyError, Diagnostic, ErrorBuf, Maybe},
    context::{Context, CtxDisplay, SymbolId},
    mir::{self, *},
    num::Uint,
    source::Span,
    store::Index,
    store::Store,
    types::{TyId, Type},
    values::Value,
};
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// Main entry point for the semantic analysis phase.
pub fn lower(ast: Ast, ctx: &mut Context) -> Result<Mir, ErrorBuf> {
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
    /// The fully typed signatures of all the functions that will be lowered
    /// into the MIR. Should these be in the MIR itself?
    sigs: Store<FnId, TypedSig>,
    pub errors: ErrorBuf,
}

impl<'mir, 'ctx> MirBuilder<'mir, 'ctx> {
    pub fn new(ast: &'mir Ast, ctx: &'mir mut Context<'ctx>) -> Self {
        let mir = Mir::new(&ast);
        let sigs = Store::with_capacity(ast.funcs.len());
        Self {
            ast,
            ctx,
            mir,
            sigs,
            errors: ErrorBuf::new(),
        }
    }

    /// Typecheck all functions in the AST, enter the lowered functions in the cfg
    pub fn lower(mut self) -> Result<Mir, ErrorBuf> {
        // First compute all of the function signatures...
        for func in self.ast.funcs.iter() {
            if let Ok(sig) = self.type_sig(&func.sig, &func.table) {
                self.sigs.insert(sig);
            }
        }

        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        // ...Then lower the functions. This separation is necessary because
        // signatures of called functions must be available during lowering.
        for (fn_id, func) in self.ast.funcs.idx_enumerate() {
            // The table argument serves to pass in the function's environment.
            let builder = GraphBuilder::new(self.ctx, &self.sigs, &self.ast, fn_id, func);
            let graph = match builder.lower() {
                Ok(gr) => gr,
                Err((gr, mut errs)) => {
                    self.errors.append(&mut errs);
                    gr
                }
            };
            let idx = self.mir.graphs.insert(graph);
            // We should check the invariant that function ids point to the same
            // function in the Mir that they do in the Ast. Bugs have caused
            // this to be violated before!
            debug_assert!(idx == fn_id);
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
            } else if cursor > 0 {
                cursor -= 1;
            } else {
                return None;
            }
        }
    }

    /// Always insert in the top table
    fn insert(&mut self, k: SymbolId, v: LocalId) -> Option<LocalId> {
        self.tables[self.current].insert(k, v)
    }
}

/// This type is used to lower a single Ast function to a Mir control-flow graph.
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
    /// The AST tables
    tables: &'mir TableStore,
    /// A "typing context" of types assigned to each expression node
    gamma: HashMap<NodeId, TyId>,
    /// The currently active basic block
    cursor: BlockId,
    /// The type signatures of all functions in the MIR
    sigs: &'mir Store<FnId, TypedSig>,
    pub errors: ErrorBuf,
}

impl<'mir, 'ctx> GraphBuilder<'mir, 'ctx> {
    pub fn new(
        ctx: &'mir mut Context<'ctx>,
        sigs: &'mir Store<FnId, TypedSig>,
        ast: &'mir Ast,
        id: FnId,
        func: &'mir Func,
    ) -> Self {
        let TypedSig { params, output, .. } = &sigs[id];

        let tables = &ast.tables;
        let table = func.table;
        let body = &ast.bodies[func.body];

        let mut gr = Graph::new(&sigs[id]);
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
            tables,
            cursor,
            sigs,
            gamma: HashMap::new(),
            errors: ErrorBuf::new(),
        }
    }

    fn error<T: 'static + Diagnostic>(&mut self, err: T) -> Maybe<()> {
        Err(self.errors.push(err))
    }

    /// Error if a type is not found in a list of expected types.
    fn expect_type(&mut self, expected: &[TyId], actual: TyId, span: Span) -> Maybe<()> {
        if !expected.contains(&actual) {
            // TODO Improve the error message by reporting /all/ of the expected
            // types, rather than just the first.
            let expected = expected[0];
            self.error(errors::ExpectedType {
                span,
                expected,
                actual,
            })?
        }
        Ok(())
    }

    // === Block-manipulating methods ===

    fn push_stmt(&mut self, stmt: mir::Stmt) {
        self.gr.push_stmt(self.cursor, stmt);
    }

    /// Push an assignment statement into the current basic block
    fn assn_stmt(&mut self, place: Place, rhs: Rvalue) {
        let stmt = mir::Stmt {
            span: Span::default(), // FIXME this is always wrong
            kind: mir::StmtKind::Assn(place, rhs),
        };
        self.push_stmt(stmt);
    }

    /// Create a new block, inheriting the satellite data of the block currently
    /// under the cursor.
    fn new_block(&mut self) -> BlockId {
        let mut block = BasicBlock::new();
        block.data = self.gr.blocks[self.cursor].data.clone();
        self.gr.blocks.insert(block)
    }

    fn set_terminator(&mut self, kind: BlockKind) {
        self.gr.blocks[self.cursor].kind = kind;
    }

    /// Temporarily work within the environment of a new goto block
    fn with_goto<T, F>(&mut self, goto: BlockId, f: F) -> Maybe<T>
    where
        F: FnOnce(&mut Self) -> Maybe<T>,
    {
        let old_block = self.cursor;
        self.cursor = self.gr.goto_block(goto);
        // On success of the internal closure, restore the block cursor and
        // return the inner value.
        f(self).map(|v| {
            self.cursor = old_block;
            v
        })
    }

    // === Lowering methods ===

    // This method either produces a graph, or a graph with some errors on the
    // side. This is a slightly awkward function signature. It doens't look like
    // any of the others in this codebase. But it's important to get *some*
    // graph out no matter what. These graphs will be stored in a linear array.
    // If we don't get a graph, we'll violate sacred invariants of the program.
    //
    // Alternative solutions would be to create a dummy graph on failure, to
    // store an `Option<Graph>` in each slot, or to keep a hash table of graphs
    // in the `Mir` data structure.
    fn lower(mut self) -> Result<Graph, (Graph, ErrorBuf)> {
        let place = self.gr.return_site().into();
        let _ = self.lower_into(&place, self.body);

        if !self.errors.is_empty() {
            Err((self.gr, self.errors))
        } else {
            Ok(self.gr)
        }
    }

    // TODO the expression match here and in `type_expr` can, and maybe should,
    // be combined into a single match. This would simplify some things: for
    // example, we wouldn't need to resolve functions twice. But mabe we can't
    // do that, since some types cannot not known without walking the tree at
    // least once.
    #[allow(unused_variables)]
    fn lower_into(&mut self, place: &Place, expr: &Expr) -> Maybe<()> {
        // FIXME possibly-unnecessary clone
        let place = place.clone();
        // We can (and must) defer type-checking of a block, since we'd
        // otherwise need to do some relatively complicated type inference.
        if !matches!(expr.data, ExprKind::Block(_)) {
            let ty_actual = self.type_expr(expr)?;
            let ty_expected = self.gr.type_of(&place, self.ctx);
            // This is now the center of all type-checking
            self.expect_type(&[ty_expected], ty_actual, expr.span)?;
        }

        match &expr.data {
            ExprKind::BinOp { left, op, right } => {
                self.lower_into_binop(place, left, op, right, expr.span)
            }
            ExprKind::UnOp { op, right } => self.lower_into_unop(place, op, right, expr.span),
            ExprKind::Assn { lhs, rhs } => self.lower_into_assn(place, lhs, rhs),
            ExprKind::Literal(lit) => self.lower_into_literal(place, lit),
            ExprKind::Ident(ident) => self.lower_into_ident(place, ident),
            ExprKind::Field { .. } => todo!(),
            ExprKind::Tuple(elems) => self.lower_into_tuple(place, elems),
            ExprKind::Struct { .. } => todo!(),
            ExprKind::IntArr { item, reps } => {
                todo!()
            }
            ExprKind::ExtArr(_) => {
                todo!()
            }
            ExprKind::Block(block) => self.lower_into_block(place, block),
            ExprKind::If { cond, tru, fls } => self.lower_into_if(place, cond, tru, fls),
            ExprKind::For { bind, iter, body } => {
                todo!()
            }
            ExprKind::Call { callee, args } => self.lower_into_call(callee, args, expr.span),
            ExprKind::Index { head, index } => {
                todo!()
            }
        }
    }

    /// Convert a place to an operand, basing the choice to move or copy on its
    /// type
    fn operand_of(&self, place: Place) -> Operand {
        // FIXME This is doing extra work to rediscover the type of this local.
        // Take a look at its call sites. I don't like it.
        let ty = &self.gr.type_of(&place, self.ctx);
        if ty.is_linear(self.ctx) {
            Operand::Move(place)
        } else {
            Operand::Copy(place)
        }
    }

    fn lower_into_binop(
        &mut self,
        place: Place,
        left: &Expr,
        op: &ast::BinOp,
        right: &Expr,
        span: Span,
    ) -> Maybe<()> {
        let ty = self.gr.locals[place.root].ty;
        // Let's assume for now that all the binops take the same two types, in
        // both arguments. This won't be true, but it's a convenient simplifying
        // assumption.
        let l_place = self.gr.auto_place(ty);
        let r_place = self.gr.auto_place(ty);

        let left = self.lower_into(&l_place, left);
        let right = self.lower_into(&r_place, right);
        if let (Err(e), _) | (_, Err(e)) = (left, right) {
            return Err(e);
        }

        let left = self.operand_of(l_place);
        let right = self.operand_of(r_place);

        let stmt = mir::Stmt {
            span: span.clone(), // FIXME actually a different span
            kind: mir::StmtKind::Assn(
                place,
                Rvalue {
                    span,
                    data: RvalueKind::BinOp(op.data, left, right),
                },
            ),
        };
        self.push_stmt(stmt);
        Ok(())
    }

    fn lower_into_unop(
        &mut self,
        place: Place,
        op: &ast::UnOp,
        right: &Expr,
        span: Span,
    ) -> Maybe<()> {
        // Should not be here, of course
        let arg_ty = self.gamma.get(&right.node).unwrap();
        let r_place = self.gr.auto_place(*arg_ty);
        self.lower_into(&r_place, right)?;

        let right = self.operand_of(r_place);
        let rhs = Rvalue {
            span,
            data: RvalueKind::UnOp(op.data, right),
        };

        let stmt = mir::Stmt {
            span: span.clone(), // FIXME actually a different span
            kind: mir::StmtKind::Assn(place, rhs),
        };
        self.push_stmt(stmt);
        Ok(())
    }

    fn lower_into_assn(&mut self, place: Place, lhs: &Expr, rhs: &Expr) -> Maybe<()> {
        // We can't *ignore* `place`, since it could be used if e.g. an assignment
        // without a terminator appears at the end of a block.
        let stmt = mir::Stmt {
            span: Span::default(), // FIXME always wrong!
            kind: mir::StmtKind::Assn(
                place,
                Rvalue {
                    span: Span::default(), // ibid
                    data: RvalueKind::Use(Operand::Const(Value::Unit)),
                },
            ),
        };
        self.push_stmt(stmt);

        let lhs = match &lhs.data {
            ExprKind::Ident(name) => name,
            _ => return Err(self.errors.push(errors::InvalidLhsKind { span: lhs.span })),
        };

        let lhs = match self.st.get(&lhs.data) {
            Some(local) => *local,
            None => return Err(self.errors.push(errors::UndeclaredLhs { span: lhs.span })),
        }
        // FIXME we'll temporarily assume that left-hand sides are just identifiers
        .into();

        self.lower_into(&lhs, rhs)
    }

    fn lower_into_literal(&mut self, place: Place, lit: &Literal) -> Maybe<()> {
        let ty = self.gr.type_of(&place, self.ctx);
        let constant = match &lit.data {
            LiteralKind::True => {
                self.expect_type(&[ty], self.ctx.common.bool, lit.span)?;
                Value::Bool(true)
            }
            LiteralKind::False => {
                self.expect_type(&[ty], self.ctx.common.bool, lit.span)?;
                Value::Bool(false)
            }
            LiteralKind::Nat(n, sz) => {
                // FIXME These downcasts are definitely not correct! Overflowing
                // literals should be an error, or at least a lint.
                let (lit_ty, val) = match sz {
                    Some(Uint::U2) => todo!(),
                    Some(Uint::U4) => todo!(),
                    Some(Uint::U8) => (self.ctx.common.u8, Value::U8(*n as u8)),
                    Some(Uint::U16) => (self.ctx.common.u16, Value::U16(*n as u16)),
                    Some(Uint::U32) => (self.ctx.common.u32, Value::U32(*n as u32)),
                    None => (self.ctx.common.u32, Value::U32(*n as u32)),
                };
                self.expect_type(&[ty], lit_ty, lit.span)?;
                val
            }
            LiteralKind::Ord => {
                self.expect_type(&[ty], self.ctx.common.ord, lit.span)?;
                Value::Ord
            }
        };
        let rhs = Rvalue {
            span: lit.span,
            data: RvalueKind::Use(Operand::Const(constant)),
        };
        self.assn_stmt(place, rhs);
        Ok(())
    }

    fn lower_into_ident(&mut self, place: Place, ident: &Ident) -> Maybe<()> {
        // NOTE Maybe this should lower unconditionally, and we should check if
        // things are declared before they're assigned as an analysis pass?
        let rhs = match self.st.get(&ident.data) {
            Some(id) => {
                // FIXME temporarily simply convert to a place
                let operand = self.operand_of((*id).into());
                Rvalue {
                    span: ident.span,
                    data: RvalueKind::Use(operand),
                }
            }
            None => {
                return self.error(errors::UnboundName {
                    span: ident.span,
                    name: ident.data,
                });
            }
        };
        self.assn_stmt(place, rhs);
        Ok(())
    }

    fn lower_into_tuple(&mut self, place: Place, elems: &[Expr]) -> Maybe<()> {
        for (field, elem) in elems.iter().enumerate() {
            let mut place = place.clone();
            place.path.push(field);
            self.lower_into(&place, elem)?;
        }
        Ok(())
    }

    /// Lower an AST block and store its value in the given location.
    fn lower_into_block(&mut self, place: Place, block: &Block) -> Maybe<()> {
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
            Some(expr) => self.lower_into(&place, expr),
            None => Ok(()),
        }
    }

    fn lower_into_if(
        &mut self,
        place: Place,
        cond: &Expr,
        tru: &Block,
        fls: &Option<Box<Block>>,
    ) -> Maybe<()> {
        // TODO: `lower_into`, and all the `lower_into_` functions, should
        // return a `Result<LocalId>`, where on success they echo back the
        // location they were lowered into. It would make this all a lot neater.
        // Could expect to get Ok(cond), then unwrap in the same match as `tru`
        // and `fls`.
        //
        // TODO: Again, I'm cheating by trying to fit this into a
        // `bool`, when it could also be a `?bool`.
        let cond_ty = self.type_expr(cond)?;
        self.expect_type(
            &[self.ctx.common.bool, self.ctx.common.q_bool],
            cond_ty,
            cond.span,
        )?;
        let cond_place = self.gr.auto_place(cond_ty);
        let cond = self.lower_into(&cond_place, cond);
        let tail_block = self.new_block();

        let mut blk_data = self.gr.blocks[self.cursor].data.clone();
        blk_data.sup_branch = Some(self.cursor);
        if cond_ty.is_linear(self.ctx) {
            blk_data.sup_lin_branch = Some(self.cursor);
        }

        // Falsy branch
        let fls = match fls {
            Some(ind) => self.with_goto(tail_block, |self_| {
                self_.gr.blocks[self_.cursor].data = blk_data.clone();
                self_.lower_into_block(place.clone(), ind)?;
                Ok(self_.cursor)
            }),
            None => Ok(tail_block),
        };

        // Truthy branch
        let tru = self.with_goto(tail_block, |self_| {
            self_.gr.blocks[self_.cursor].data = blk_data;
            self_.lower_into_block(place, tru)?;
            Ok(self_.cursor)
        });

        // Propagate errors from branches
        let (tru, fls, _) = match (tru, fls, cond) {
            (Ok(tru), Ok(fls), Ok(cond)) => Ok((tru, fls, cond)),
            (Err(err), _, _) | (_, Err(err), _) | (_, _, Err(err)) => Err(err),
        }?;

        let switch = BlockKind::Switch {
            cond: cond_place,
            blks: vec![fls, tru],
        };
        self.set_terminator(switch);
        self.cursor = tail_block;
        Ok(())
    }

    // We need to be a little careful about how we treat the arguments here. In
    // particular, there should probably be a distinction between passing by
    // value and passing by reference, which for the time being isn't respected.
    //
    // Also, we probably want the callee to be an expression rather than a function name.
    fn lower_into_call(&mut self, callee: &Ident, args: &Vec<Expr>, span: Span) -> Maybe<()> {
        // FIXME Note that we're resolving every function twice, which suggests
        // that this could be pulled up to an earlier stage, and that it's a
        // potential source of errors.
        let func = self.resolve_function(&callee.data).unwrap();
        let func_sig = &self.sigs[func];
        let arg_locals: Vec<_> = func_sig
            .params
            .iter()
            .map(|(_symb, ty)| {
                let local = self.gr.auto_place(*ty);
                // Call by value!
                self.operand_of(local)
            })
            .collect();

        for (arg, operand) in args.into_iter().zip(arg_locals.iter()) {
            if let Operand::Copy(loc) | Operand::Move(loc) = operand {
                self.lower_into(loc, arg)?;
            }
        }

        let tail_block = self.new_block();
        let call = BlockKind::Call {
            callee: func,
            args: arg_locals,
            blk: tail_block,
            span,
        };
        self.set_terminator(call);
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
                let place = self.gr.auto_place(self.ctx.common.unit);
                self.lower_into(&place, expr)
            }
            StmtKind::Decl { lhs, ty, rhs } => self.lower_decl(lhs, ty, rhs),
        }
    }

    fn lower_decl(
        &mut self,
        lhs: &Pattern,
        ty: &Option<Annot>,
        rhs: &Option<Box<Expr>>,
    ) -> Maybe<()> {
        // FIXME Just unwrap the pattern, which for now can only be an identifier
        let (lhs_data, lhs_span) = match lhs.data {
            PatternKind::Ident(ident) => (ident, lhs.span),
        };

        // Is this annotated, or must we infer the type?
        let ty = match (ty, rhs) {
            // This should work, rather than emit an error, if we ever
            // have proper type inferece!
            (None, None) => {
                return Err(self.errors.push(errors::InferenceFailure {
                    span: lhs_span,
                    name: lhs_data,
                }))
            }
            (Some(ty), _) => typing::resolve_type(ty, &self.table, self.ctx)?,
            (_, Some(rhs)) => self.type_inner(rhs)?,
        };
        let place = self.gr.user_place(ty);
        if let Some(rhs) = rhs {
            self.lower_into(&place, rhs)?;
        }
        self.st.insert(lhs_data, place.root);
        Ok(())
    }

    fn resolve_function(&self, func: &SymbolId) -> Option<FnId> {
        let tab = &self.tables[self.table];
        tab.funcs.get(func).copied()
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

    /// We're not doing full type inference, but we do need to know what to do
    /// when we call a function and ignore its return value. Or, when we move a
    /// variable into a new binding that doesn't have an annotation. These
    /// methods provide the "ad hoc," weak type inference needed to lower such
    /// expressions. Note that we're spreading out type checking and inference
    /// across this file, so it might be ugly to clean up later.
    ///
    /// Also note that all this is a horribly inefficient stopgap.
    impl<'mir, 'ctx> GraphBuilder<'mir, 'ctx> {
        pub fn type_expr(&mut self, expr: &Expr) -> Maybe<TyId> {
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
                ExprKind::Assn { .. } => self.ctx.common.unit,
                ExprKind::Literal(lit) => self.type_literal(lit)?,
                ExprKind::Ident(ident) => self.type_ident(ident)?,
                ExprKind::Field { .. } => todo!(),
                ExprKind::Tuple(elems) => self.type_tuple(elems)?,
                ExprKind::Struct { ty, .. } => todo!(),
                ExprKind::IntArr { item, reps } => todo!(),
                ExprKind::ExtArr(_) => todo!(),
                ExprKind::Block(block) => self.type_block(block)?,
                ExprKind::If {
                    cond,
                    tru: dir,
                    fls: ind,
                } => self.type_if(cond, dir, ind)?,
                ExprKind::For { bind, iter, body } => self.ctx.common.unit,
                // FIXME note that here we are resolving this function a *second*
                // time (the other is in the lowering method). This suggests
                // that we should factor out function resolution to some earlier
                // step. It might even be a good idea to use an HIR or
                // something, which is typed and fully-resolved, but not yet
                // lowered to a control-flow graph.
                ExprKind::Call { callee, args } => {
                    let func = self.resolve_function(&callee.data).ok_or_else(|| {
                        self.errors.push(errors::UnboundName {
                            span: callee.span,
                            name: callee.data,
                        })
                    })?;
                    let sig = &self.sigs[func];
                    sig.output
                }
                ExprKind::Index { head, index } => todo!(),
            };
            self.gamma.insert(expr.node, ty);
            Ok(ty)
        }

        fn type_binop(&mut self, left: &Expr, op: &ast::BinOp, right: &Expr) -> Maybe<TyId> {
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
                UnOpKind::Delin => {
                    if right == self.ctx.common.q_bool {
                        Ok(self.ctx.common.bool)
                    } else if right == self.ctx.common.q_u4 {
                        Ok(self.ctx.common.u4)
                    } else if right == self.ctx.common.q_u8 {
                        Ok(self.ctx.common.u8)
                    } else if right == self.ctx.common.q_u16 {
                        Ok(self.ctx.common.u16)
                    } else if right == self.ctx.common.q_u32 {
                        Ok(self.ctx.common.u32)
                    } else {
                        Err(self.errors.push(errors::UnOpOutTypeError {
                            span: op.span,
                            kind: op.data,
                            ty: right,
                        }))
                    }
                }
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
                LiteralKind::Ord => self.ctx.common.ord,
            };
            Ok(ty)
        }

        fn type_block(&mut self, block: &Block) -> Maybe<TyId> {
            // FIXME This is manifestly incorrect.
            match &block.expr {
                Some(expr) => self.type_inner(expr),
                None => Ok(self.ctx.common.unit),
            }
        }

        fn type_if(&mut self, cond: &Expr, dir: &Block, ind: &Option<Box<Block>>) -> Maybe<TyId> {
            let ty_dir = self.type_block(dir)?;
            let ty_ind = if let Some(blk) = ind {
                self.type_block(blk)?
            } else {
                self.ctx.common.unit
            };

            if ty_dir == ty_ind {
                Ok(ty_ind)
            } else {
                Err(self.errors.push(errors::IfIncompatibleTypes {
                    span: cond.span,
                    dir: ty_dir,
                    ind: ty_ind,
                }))
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

        fn type_tuple(&mut self, elems: &[Expr]) -> Maybe<TyId> {
            let tys = elems
                .iter()
                .map(|elem| self.type_expr(elem))
                .collect::<Maybe<Vec<TyId>>>()?;
            let ty = self.ctx.types.intern(Type::Tuple(tys));
            Ok(ty)
        }
    }

    /// Resolve an annotation to a type, given a table (scope) in which it
    /// should appear. This should eventually be farmed out to a type inference
    /// module/crate, and/or appear earlier in the compilaton process. For now it doesn't hurt to include here.
    pub fn resolve_type<'a>(annot: &Annot, tab: &TableId, ctx: &mut Context<'a>) -> Maybe<TyId> {
        let ty = match &annot.data {
            AnnotKind::Bool => ctx.common.bool,
            AnnotKind::Uint(u) => match u {
                Uint::U2 => unimplemented!(),
                Uint::U4 => ctx.common.u4,
                Uint::U8 => ctx.common.u8,
                Uint::U16 => ctx.common.u16,
                Uint::U32 => ctx.common.u32,
            },
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
            AnnotKind::Ident(_) => {
                todo!();
            }
            AnnotKind::Func(params, ret) => {
                let param_tys = params
                    .iter()
                    .map(|ann| resolve_type(ann, tab, ctx))
                    .collect::<Maybe<Vec<TyId>>>()?;
                let ret_ty = resolve_type(ret, tab, ctx)?;
                ctx.types.intern(Type::Func(param_tys, ret_ty))
            }
            AnnotKind::Ord => ctx.common.ord,
        };

        Ok(ty)
    }

    fn resolve_annot_question(ctx: &mut Context, inner: TyId) -> Maybe<TyId> {
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
    #[msg = "expected type `{expected}`, found `{actual}`"]
    pub struct ExpectedType {
        #[span]
        pub span: Span,
        #[ctx]
        pub expected: TyId,
        #[ctx]
        pub actual: TyId,
    }

    /// TODO This error should go in a type inference model when the day comes
    /// that we add HM type inference to the language.
    #[derive(Diagnostic)]
    #[msg = "could not infer a type for `{name}`"]
    pub struct InferenceFailure {
        #[span]
        pub span: Span,
        #[ctx]
        pub name: SymbolId,
    }

    #[derive(Diagnostic)]
    #[msg = "operator `{kind}` doesn't support argument types `{left}` and `{right}`"]
    pub struct BinOpTypeError {
        #[span]
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
    #[msg = "operator `{kind}` doesn't support argument type `{right}`"]
    pub struct UnOpArgTypeError {
        #[span]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual right operand type
        #[ctx]
        pub right: TyId,
    }

    #[derive(Diagnostic)]
    #[msg = "operator `{kind}` doesn't support output type `{ty}`"]
    pub struct UnOpOutTypeError {
        #[span]
        pub span: Span,
        /// The operator
        pub kind: UnOpKind,
        /// The actual output type
        #[ctx]
        pub ty: TyId,
    }

    #[derive(Diagnostic)]
    #[msg = "pattern fails to match type `{actual}`"]
    pub struct DestructuringError {
        #[span]
        pub span: Span,
        /// The type
        #[ctx]
        pub actual: TyId,
    }

    #[derive(Diagnostic)]
    #[msg = "element's type differs from `{ty}`"]
    pub struct HeterogeneousArray {
        #[span]
        pub span: Span,
        #[ctx]
        pub ty: TyId,
    }

    #[derive(Diagnostic)]
    #[msg = "expected size type, found `{ty}`"]
    pub struct ExpectedSizeType {
        #[span]
        pub span: Span,
        #[ctx]
        pub ty: TyId,
    }

    #[derive(Diagnostic)]
    #[msg = "name `{name}` is not bound"]
    pub struct UnboundName {
        #[span]
        pub span: Span,
        #[ctx]
        pub name: SymbolId,
    }

    #[derive(Diagnostic)]
    #[msg = "cannot assign to nonexistent location"]
    pub struct UndeclaredLhs {
        #[span]
        #[span(msg = "try declaring this first")]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "invalid left-hand side of assignment"]
    pub struct InvalidLhsKind {
        #[span(msg = "expected a variable here")]
        pub span: Span,
    }

    // NOTE this error message could be more helpful: the single span points to
    // the condition. There should be spans for each of the return types.
    #[derive(Diagnostic)]
    #[msg = "incompatible types in conditional branches: found `{dir}` and `{ind}`"]
    pub struct IfIncompatibleTypes {
        #[span]
        pub span: Span,
        #[ctx]
        pub dir: TyId,
        #[ctx]
        pub ind: TyId,
    }
}
