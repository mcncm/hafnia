//! FIXME This module is trying to do too much. It's overly complex, and will be
//! hard for anyone else to understand. Once again, rustc did this right: this
//! should be divided into two passes: a first in which everything is fully
//! resolved, and a second in which we actually lower statements.

use crate::{
    ast::{self, StmtKind, *},
    cavy_errors::{CavyError, Diagnostic, ErrorBuf, Maybe},
    context::{Context, SymbolId},
    mir::{self, FnCall, *},
    num::Uint,
    source::Span,
    store::Index,
    store::Store,
    types::{Discriminant, RefKind, TyId, Type, TypeSize, UserType},
    util::FmtWith,
    values::Value,
};
use std::collections::HashMap;

/// Main entry point for the semantic analysis phase.
pub fn lower(ast: Ast, ctx: &mut Context) -> Result<Mir, ErrorBuf> {
    MirBuilder::new(&ast, ctx).lower()
}

/// This struct handles lowering from the Ast to the Mir.
pub struct MirBuilder<'mir, 'ctx> {
    ast: &'mir Ast,
    /// Translation table for user-defined types, whose `UdtId` are erased in
    /// the MIR.
    udt_tys: HashMap<UdtId, TyId>,
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
        let udt_tys = HashMap::new();
        Self {
            ast,
            udt_tys,
            ctx,
            mir,
            sigs,
            errors: ErrorBuf::new(),
        }
    }

    /// Turn an AST struct definition into a concrete type
    fn resolve_struct(&mut self, struct_: &Struct, table: &Table) -> Maybe<TyId> {
        let fields: Vec<_> = struct_
            .fields
            .iter()
            .map(|field| {
                let name = field.name.data;
                let ty = self.resolve_annot(&field.ty, table)?;
                Ok((name, ty))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let udt = UserType {
            def_name: struct_.name.data,
            fields,
            tag: None,
        };

        let ty = self.ctx.intern_ty(Type::UserType(udt));
        Ok(ty)
    }

    /// Turn an AST enum definition into a concrete type
    fn resolve_enum(&mut self, enum_: &Enum, table: &Table) -> Maybe<TyId> {
        let mut fields = Vec::new();
        let mut sz = TypeSize::zero();
        for variant in enum_.variants.iter() {
            let name = variant.name.data;
            let ty = match &variant.data {
                Some(Spanned { data: annots, .. }) => {
                    let tys = annots
                        .iter()
                        .map(|ty| self.resolve_annot(ty, table))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(self.ctx.intern_ty(Type::Tuple(tys)))
                }
                None => Ok(self.ctx.common.unit),
            }?;
            sz = sz.join_max(ty.size(self.ctx));
            fields.push((name, ty));
        }

        // For now, only classical tags will be possible.
        let tagsize = util::bitsize(fields.len());
        let tag = Some(Discriminant::C(tagsize));

        let udt = UserType {
            def_name: enum_.name.data,
            fields,
            tag,
        };

        let ty = self.ctx.intern_ty(Type::UserType(udt));
        Ok(ty)
    }

    /// Resolve things stored in global tables: function type signatures,
    /// user-defined types, and so on.
    fn resolve_global(&mut self) -> Result<(), ()> {
        // Resolve user-defined types
        for (id, udt) in self.ast.udts.idx_enumerate() {
            let table = &self.ast.tables[udt.table];
            match &udt.kind {
                UdtKind::Struct(struct_) => {
                    if let Ok(ty) = self.resolve_struct(struct_, table) {
                        self.udt_tys.insert(id, ty);
                    }
                }
                UdtKind::Enum(enum_) => {
                    if let Ok(ty) = self.resolve_enum(enum_, table) {
                        self.udt_tys.insert(id, ty);
                    }
                }
                UdtKind::Alias(annot) => {
                    if let Ok(ty) = self.resolve_annot(annot, table) {
                        self.udt_tys.insert(id, ty);
                    }
                }
            }
        }

        // Then compute all of the function signatures...
        for func in self.ast.funcs.iter() {
            let table = &self.ast.tables[func.table];
            if let Ok(sig) = self.type_sig(&func.sig, table) {
                self.sigs.insert(sig);
            }
        }

        if !self.errors.is_empty() {
            Err(())
        } else {
            Ok(())
        }
    }

    /// Typecheck all functions in the AST, enter the lowered functions in the cfg
    pub fn lower(mut self) -> Result<Mir, ErrorBuf> {
        if let Err(_) = self.resolve_global() {
            return Err(self.errors);
        }

        // ...Then lower the functions. This separation is necessary because
        // signatures of called functions must be available during lowering.
        for (fn_id, func) in self.ast.funcs.idx_enumerate() {
            // The table argument serves to pass in the function's environment.
            let builder =
                GraphBuilder::new(self.ctx, &self.sigs, &self.ast, &self.udt_tys, fn_id, func);
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
            self.mir.graph_data.insert(self.graph_data(fn_id));
        }
        debug_assert_eq!(self.mir.graphs.len(), self.mir.graph_data.len());

        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            Ok(self.mir)
        }
    }

    fn graph_data(&self, fn_id: FnId) -> GraphData {
        let func = &self.ast.funcs[fn_id];
        GraphData {
            is_unsafe: func.is_unsafe,
            is_rev: false,
            def_name: func.def_name,
        }
    }

    /// Resolve the types in a function signature
    pub fn type_sig(&mut self, sig: &Sig, tab: &Table) -> Maybe<TypedSig> {
        let params = sig
            .params
            .iter()
            .map(|p| {
                let ty = self.resolve_annot(&p.ty, tab);
                Ok((p.name.data, ty?))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output = match &sig.output {
            None => self.ctx.intern_ty(Type::unit()),
            Some(annot) => self.resolve_annot(annot, tab)?,
        };
        let sig = TypedSig {
            params,
            output,
            span: sig.span,
        };
        Ok(sig)
    }

    // FIXME this convenience method just wraps `typing::resolve_type` to supply
    // its bevy of arguments.
    fn resolve_annot(&mut self, ty: &Annot, tab: &Table) -> Maybe<TyId> {
        typing::resolve_annot(
            ty,
            tab,
            &self.ast.tables,
            &self.udt_tys,
            &mut self.errors,
            &mut self.ctx,
        )
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

    /// NOTE: this is actually incorrect, because of how it should interact with
    /// function scope.
    ///
    /// NOTE: (again) what does the comment above mean?
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
    /// User-defined type translation table
    udt_tys: &'mir HashMap<UdtId, TyId>,
    /// A stack of locals tables
    st: SymbolTable,
    /// The currently active items table
    table: TableId,
    /// The AST items tables
    tables: &'mir TableStore,
    /// A "typing context" of types assigned to each expression node
    gamma: HashMap<NodeId, TyId>,
    /// The currently active basic block
    cursor: BlockId,
    /// If the currently active scope is contained in an `unsafe` block
    in_unsafe: bool,
    /// The type signatures of all functions in the MIR
    sigs: &'mir Store<FnId, TypedSig>,
    pub errors: ErrorBuf,
}

impl<'mir, 'ctx> GraphBuilder<'mir, 'ctx> {
    pub fn new(
        ctx: &'mir mut Context<'ctx>,
        sigs: &'mir Store<FnId, TypedSig>,
        ast: &'mir Ast,
        udt_tys: &'mir HashMap<UdtId, TyId>,
        id: FnId,
        func: &'mir Func,
    ) -> Self {
        let TypedSig { params, output, .. } = &sigs[id];

        let tables = &ast.tables;
        let table = func.table;
        let body = &ast.bodies[func.body];

        let mut gr = Graph::new(id, &sigs[id]);
        let mut st = SymbolTable::new();
        let cursor = gr.entry_block;

        gr.locals.insert(Local {
            ty: *output,
            kind: LocalKind::Param,
        });

        for (param, ty) in params {
            let local = gr.locals.insert(Local {
                ty: *ty,
                kind: LocalKind::Param,
            });
            st.insert(*param, local);
        }

        Self {
            ctx,
            body,
            gr,
            udt_tys,
            st,
            table,
            tables,
            cursor,
            sigs,
            in_unsafe: false,
            gamma: HashMap::new(),
            errors: ErrorBuf::new(),
        }
    }

    fn error<E: 'static + Diagnostic, T>(&mut self, err: E) -> Maybe<T> {
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

    fn push_stmt(&mut self, span: Span, stmt: mir::StmtKind) {
        let scope_data = ScopeData {
            in_unsafe: self.in_unsafe,
        };
        let stmt = mir::Stmt {
            span,
            scope_data,
            kind: stmt,
        };
        self.gr.push_stmt(self.cursor, stmt);
    }

    /// Push an assignment statement into the current basic block
    fn assn_stmt(&mut self, place: Place, rhs: Rvalue) {
        let span = rhs.span;
        let stmt = mir::StmtKind::Assn(place, rhs);
        self.push_stmt(span, stmt);
    }

    // NOTE: This is the only call site of `Graph::insert_block`, and it's only
    // needed to carry around this satellite data you don't want. You can get rid of both.
    /// Create a new block with the same tail data as the cursor.
    fn new_block(&mut self) -> BlockId {
        let mut block = BasicBlock::new();
        block.kind = match self.gr[self.cursor].kind {
            BlockKind::Goto(blk) => BlockKind::Goto(blk),
            BlockKind::Ret => BlockKind::Ret,
            // this is just an assertion about where this method will be called
            // from.
            _ => unreachable!(),
        };
        self.gr.insert_block(block)
    }

    fn set_terminator(&mut self, kind: BlockKind) {
        self.gr[self.cursor].kind = kind;
    }

    /// The partner of Parser::with_table at the next stage of the compilation
    /// pipeline.
    fn with_scope<T, F>(&mut self, new: TableId, is_unsafe: bool, f: F) -> Maybe<T>
    where
        F: FnOnce(&mut Self) -> Maybe<T>,
    {
        let old_table = self.table;
        self.table = new;
        let old_unsafe = self.in_unsafe;
        self.in_unsafe = is_unsafe;
        let restore = |this: &mut Self| {
            this.in_unsafe = old_unsafe;
            this.table = old_table;
            this.st.pop_table();
        };
        self.st.push_table();
        let t = match f(self) {
            Ok(t) => t,
            Err(err) => {
                restore(self);
                return Err(err);
            }
        };
        restore(self);
        Ok(t)
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
        let place = Graph::return_site().into();
        let _ = self.lower_into(&place, self.body);
        // NOTE: is this always correct?
        self.gr.exit_block = self.cursor;

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
            ExprKind::Assn { op, lhs, rhs } => self.lower_into_assn(place, op, lhs, rhs),
            ExprKind::Literal(lit) => self.lower_into_literal(place, lit),
            ExprKind::Ident(ident) => self.lower_into_ident(place, ident),
            ExprKind::Field(root, field) => self.lower_into_field(place, root, field),
            ExprKind::Tuple(elems) => self.lower_into_tuple(place, elems),
            ExprKind::Struct { ty, fields } => self.lower_into_struct(place, ty, fields),
            ExprKind::IntArr { item, reps } => {
                todo!()
            }
            ExprKind::ExtArr(_) => {
                todo!()
            }
            ExprKind::Block(block) => self.lower_into_block(place, block),
            ExprKind::If { cond, tru, fls } => self.lower_into_if(place, cond, tru, fls),
            ExprKind::Match { .. } => todo!(),
            ExprKind::For { bind, iter, body } => {
                todo!()
            }
            ExprKind::Call { callee, args } => self.lower_into_call(place, callee, args, expr.span),
            ExprKind::Index { head, index } => {
                todo!()
            }
            ExprKind::Ref { annot, expr: inner } => {
                self.lower_into_ref(place, annot, inner, expr.span)
            }
            ExprKind::Deref(inner) => {
                let rplace = self.resolve_deref(inner)?;
                let rvalue = Rvalue {
                    data: RvalueKind::Use(self.operand_of(rplace)),
                    span: expr.span,
                };
                self.assn_stmt(place, rvalue);
                Ok(())
            }
        }
    }

    /// Lower an expression, possibly generating new temp variables to store it in.
    fn lower_expr(&mut self, expr: &Expr) -> Maybe<Place> {
        // We don't want to generate new temp variables for (lexical)
        // variables--they'll get lost! Otherwise, this would be a problem when
        // we take references.
        if let ExprKind::Ident(ref ident) = expr.data {
            return self.resolve_ident(ident);
        }
        let ty = self.type_expr(expr)?;
        let place = self.gr.auto_place(ty);
        self.lower_into(&place, expr)?;
        Ok(place)
    }

    /// Convert a place to an operand, basing the choice to move or copy on its
    /// type
    fn operand_of(&self, place: Place) -> Operand {
        // FIXME This is doing extra work to rediscover the type of this local.
        // Take a look at its call sites. I don't like it.
        let ty = &self.gr.type_of(&place, self.ctx);
        if ty.is_affine(self.ctx) {
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
        let l_place = self.lower_expr(left)?;
        let r_place = self.lower_expr(right)?;

        let left = self.operand_of(l_place);
        let right = self.operand_of(r_place);

        let stmt = mir::StmtKind::Assn(
            place,
            Rvalue {
                span,
                data: RvalueKind::BinOp(op.data, left, right),
            },
        );
        // FIXME: actually a different span
        self.push_stmt(span, stmt);
        Ok(())
    }

    fn lower_into_unop(
        &mut self,
        place: Place,
        op: &ast::UnOp,
        right: &Expr,
        span: Span,
    ) -> Maybe<()> {
        let r_place = self.lower_expr(right)?;

        let right = self.operand_of(r_place);
        let rhs = Rvalue {
            span,
            data: RvalueKind::UnOp(op.data, right),
        };

        // FIXME: actually a different span
        self.push_stmt(span, mir::StmtKind::Assn(place, rhs));
        Ok(())
    }

    /// Lower an assignment *expression*, as on the rhs of `let x = (y = 2);`.
    fn lower_into_assn(&mut self, place: Place, op: &AssnOp, lhs: &Expr, rhs: &Expr) -> Maybe<()> {
        // We can't *ignore* `place`, since it could be used if e.g. an assignment
        // without a terminator appears at the end of a block.
        let span = lhs.span.join(&rhs.span).unwrap();
        let stmt = mir::StmtKind::Assn(place, Rvalue::unit());
        self.push_stmt(span, stmt);

        let lhs = match &lhs.data {
            // This unwrap *should* be safe because the name is validated during
            // typechecking
            ExprKind::Ident(name) => (*self.st.get(&name.data).unwrap()).into(),
            ExprKind::Field(root, field) => self.resolve_fields(root, field)?,
            ExprKind::Deref(inner) => self.resolve_deref(inner)?,
            _ => return Err(self.errors.push(errors::InvalidLhsKind { span: lhs.span })),
        };

        let binop = match op.data {
            AssnOpKind::Equal => return self.lower_into(&lhs, rhs),
            AssnOpKind::And => BinOpKind::And,
            AssnOpKind::Or => BinOpKind::Or,
            AssnOpKind::Xor => BinOpKind::Xor,
        };

        // This was not an `Equal` assignment; do the operation and store it
        // *back* in the lhs.
        let rhs = self.lower_expr(rhs)?;
        let rvalue_kind = RvalueKind::BinOp(
            binop,
            self.operand_of(lhs.clone()),
            self.operand_of(rhs.clone()),
        );
        let rvalue = Rvalue {
            span,
            data: rvalue_kind,
        };
        self.assn_stmt(lhs, rvalue);
        Ok(())
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
        let rplace = self.resolve_ident(ident)?;
        let operand = self.operand_of(rplace);
        let rhs = Rvalue {
            span: ident.span,
            data: RvalueKind::Use(operand),
        };
        self.assn_stmt(place, rhs);
        Ok(())
    }

    // Ok, maybe not the best function name, but this is how we get the place
    // that an identifier refers to.
    fn resolve_ident(&mut self, ident: &Ident) -> Maybe<Place> {
        match self.st.get(&ident.data) {
            Some(id) => Ok(Place::from(*id)),
            None => self.error(errors::UnboundName {
                span: ident.span,
                name: ident.data,
            }),
        }
    }

    fn lower_into_field(&mut self, place: Place, head: &Expr, field: &Field) -> Maybe<()> {
        let rhs = self.resolve_fields(head, field)?;
        let rhs = Rvalue {
            // FIXME Throughout this module, there are a lot of places where I
            // should be propagating spans downward, but I end up dropping,
            // approximating, or reconstructing them (as here).
            span: head.span.join(&field.span).unwrap(),
            data: RvalueKind::Use(self.operand_of(rhs)),
        };
        self.assn_stmt(place, rhs);
        Ok(())
    }

    /// An odd method, different from all the others of this struct--except,
    /// now, `resolve_ident`. The goal is to unroll a linked-list-like sequence
    /// of field accesses into a single path
    fn resolve_fields(&mut self, head: &Expr, field: &Field) -> Maybe<Place> {
        let head_ty = self.type_expr(head)?;
        let mut place = match &head.data {
            ExprKind::Ident(ident) => {
                // This unwrap is maybe safe? I'm not actually sure why. It's
                // checked earlier somewhere.
                let id = self.st.get(&ident.data).unwrap();
                (*id).into()
            }
            ExprKind::Field(head, field) => self.resolve_fields(head, &field)?,
            _ => {
                let head_place = self.gr.auto_place(head_ty);
                self.lower_into(&head_place, head)?;
                head_place
            }
        };
        let (field, _) = self.field_of(head_ty, field).unwrap();
        place.path.push(Proj::Field(field));
        Ok(place)
    }

    /// Ok, now a third of these odd methods
    fn resolve_deref(&mut self, inner: &Expr) -> Maybe<Place> {
        let mut rplace = self.lower_expr(inner)?;
        rplace.path.push(Proj::Deref);
        Ok(rplace)
    }

    fn lower_into_tuple(&mut self, place: Place, elems: &[Expr]) -> Maybe<()> {
        for (field, elem) in elems.iter().enumerate() {
            let mut place = place.clone();
            place.path.push(Proj::Field(field));
            self.lower_into(&place, elem)?;
        }
        Ok(())
    }

    fn lower_into_struct(
        &mut self,
        place: Place,
        name: &Ident,
        fields: &[(Ident, Expr)],
    ) -> Maybe<()> {
        let ty = self.resolve_type(&name.data).unwrap();
        // We have to fully-resolve the type again, but this time *just* to get
        // the fields into the right order.
        let udt = match &self.ctx.types[ty] {
            Type::UserType(udt) => udt,
            _ => unreachable!(),
        };
        let fields: HashMap<SymbolId, &Expr> = fields.iter().map(|(k, v)| (k.data, v)).collect();
        // FIXME Horror! A completely unnecessary clone. The trouble here is
        // that we're immutably borrowing &self up above, in order to get the
        // struct specification in the first place. Down below, we're calling
        // `lower_into`, which requires a `&mut self`. And, you know what, the
        // borrow checker is correct: the `udt` reference could be invalidated
        // during `lower_into`, since it might well insert new types into the
        // `Context`. I wonder if there's *any* reasonable way around this
        // clone.
        //
        // I'm giving up performance left and right for the sake of getting this
        // working, but it's a problem for another day.
        let udt_fields = udt.fields.clone();

        for (n, (field, _)) in udt_fields.iter().enumerate() {
            let expr = match fields.get(field) {
                Some(expr) => expr,
                None => {
                    return Err(self.errors.push(errors::MissingStructField {
                        span: name.span,
                        name: name.data,
                        field: *field,
                    }))
                }
            };
            let mut place = place.clone();
            place.path.push(Proj::Field(n));
            self.lower_into(&place, expr)?;
        }
        Ok(())
    }

    /// Lower an AST block and store its value in the given location.
    fn lower_into_block(&mut self, place: Place, block: &Block) -> Maybe<()> {
        self.with_scope(block.table, block.is_unsafe, |this| {
            Self::lower_into_block_inner(this, place, block)
        })
    }

    fn lower_into_block_inner(&mut self, place: Place, block: &Block) -> Maybe<()> {
        let Block {
            stmts,
            expr,
            table: _,     // already taken care of by outer function
            is_unsafe: _, // TODO must check for any unsafe operations, etc.
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
            None => {
                // FIXME This would be better if we made an artifical AST
                // node containing the return value, then just called
                // `lower_into` on it.
                //
                // In any case, this block is a mess that needs to be cleaned up.
                let ty_expected = self.gr.type_of(&place, self.ctx);
                let mut span = *span;
                span.start = span.end; // Just get the closing bracket
                self.expect_type(&[ty_expected], self.ctx.common.unit, span)?;
                let rhs = Rvalue {
                    data: RvalueKind::Use(Operand::Const(Value::Unit)),
                    span,
                };
                self.assn_stmt(place, rhs);
                Ok(())
            }
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
        let span = cond.span;
        self.expect_type(
            &[self.ctx.common.bool, self.ctx.common.shrd_q_bool],
            cond_ty,
            cond.span,
        )?;
        let cond_place = self.gr.auto_place(cond_ty);
        let cond = self.lower_into(&cond_place, cond);

        // The tail should be a new block that's going wherever the current
        // block was going.
        let tail_block = self.new_block();

        // Falsey branch
        let fls = self.with_goto(tail_block, |this| {
            // Capture a pointer to the *first* block on the branch, before
            // any further lowering.
            let branch = this.cursor;
            if let Some(fls) = fls {
                this.lower_into_block(place.clone(), fls)?;
            } else {
                // We still have to put something in that `Place`!.
                this.assn_stmt(place.clone(), Rvalue::unit());
            }
            Ok(branch)
        });

        // Truthy branch
        let tru = self.with_goto(tail_block, |this| {
            let branch = this.cursor;
            this.lower_into_block(place, tru)?;
            Ok(branch)
        });

        // Propagate errors from branches
        let (tru, fls, _) = match (tru, fls, cond) {
            (Ok(tru), Ok(fls), Ok(cond)) => Ok((tru, fls, cond)),
            (Err(err), _, _) | (_, Err(err), _) | (_, _, Err(err)) => Err(err),
        }?;

        let switch = Switch {
            cond: cond_place,
            span,
            blks: vec![fls, tru],
        };
        let kind = BlockKind::Switch(Box::new(switch));
        self.set_terminator(kind);
        self.cursor = tail_block;
        Ok(())
    }

    // We need to be a little careful about how we treat the arguments here. In
    // particular, there should probably be a distinction between passing by
    // value and passing by reference, which for the time being isn't respected.
    //
    // Also, we probably want the callee to be an expression rather than a function name.
    fn lower_into_call(
        &mut self,
        place: Place,
        callee: &Ident,
        args: &[Expr],
        span: Span,
    ) -> Maybe<()> {
        // FIXME Note that we're resolving every function twice, which suggests
        // that this could be pulled up to an earlier stage, and that it's a
        // potential source of errors.
        let func = self.resolve_function(&callee.data).unwrap();
        let func_sig = &self.sigs[func];
        let args: Vec<_> = func_sig
            .params
            .iter()
            .zip(args)
            .map(|((_symb, ty), arg)| {
                let place = self.gr.auto_place(*ty);
                self.lower_into(&place, arg)?;
                // Call by value!
                Ok(self.operand_of(place))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let tail_block = self.new_block();
        let scope_data = ScopeData {
            in_unsafe: self.in_unsafe,
        };
        let call = BlockKind::Call(Box::new(FnCall {
            callee: func,
            args,
            ret: place,
            blk: tail_block,
            scope_data,
            span,
        }));
        self.set_terminator(call);
        self.cursor = tail_block;
        Ok(())
    }

    fn lower_into_ref(
        &mut self,
        place: Place,
        annot: &RefAnnot,
        expr: &Expr,
        span: Span,
    ) -> Maybe<()> {
        // Lower the rhs
        let r_place = self.lower_expr(expr)?;

        // No lifetime annotation in a borrow expression
        if let Some(lt) = &annot.lifetime {
            return Err(self
                .errors
                .push(errors::LifetimeInBorrow { span, name: lt.0 }));
        }

        // Get the reference kind
        let ref_kind = typing::resolve_ref_annot(annot);

        // Finally, put it there
        let rvalue = Rvalue {
            data: RvalueKind::Ref(ref_kind, r_place),
            span,
        };
        self.assn_stmt(place, rvalue);
        Ok(())
    }

    fn lower_stmt(&mut self, stmt: &ast::Stmt) -> Maybe<()> {
        match &stmt.data {
            StmtKind::Io(io) => self.lower_io_stmt(io, stmt.span),
            StmtKind::Assert(expr) => self.lower_assert_stmt(expr, stmt.span),
            StmtKind::Drop(expr) => self.lower_drop_stmt(expr, stmt.span),
            StmtKind::Expr(expr) | StmtKind::ExprSemi(expr) => {
                // ...Make something up, for now? But in fact, you'll have to do
                // some kind of "weak"/"ad hoc" type inference to get this type.
                let ty = self.type_expr(expr)?;
                let place = self.gr.auto_place(ty);
                self.lower_into(&place, expr)
            }
            StmtKind::Decl { lhs, ty, rhs } => self.lower_decl(lhs, ty, rhs),
        }
    }

    fn lower_io_stmt(&mut self, io: &ast::IoStmtKind, span: Span) -> Maybe<()> {
        match io {
            ast::IoStmtKind::In => unimplemented!(),
            ast::IoStmtKind::Out { lhs, name } => {
                // ...Make something up, for now? But in fact, you'll have to do
                // some kind of "weak"/"ad hoc" type inference to get this type.
                let ty = match self.type_expr(lhs) {
                    Ok(ty) => ty,
                    Err(_) => Err(self.errors.push(errors::InferenceFailure {
                        span: name.span,
                        name: name.data,
                    }))?,
                };
                let place = self.gr.auto_place(ty);
                self.lower_into(&place, lhs)?;
                let stmt = mir::IoStmtKind::Out {
                    place,
                    symb: name.data,
                };
                self.push_stmt(span, mir::StmtKind::Io(stmt));
                Ok(())
            }
        }
    }

    fn lower_assert_stmt(&mut self, expr: &Expr, span: Span) -> Maybe<()> {
        let place = self.lower_expr(expr)?;
        self.push_stmt(span, mir::StmtKind::Assert(place));
        Ok(())
    }

    fn lower_drop_stmt(&mut self, expr: &Expr, span: Span) -> Maybe<()> {
        if let ExprKind::Ident(_) | ExprKind::Field(_, _) = expr.data {
            let place = self.lower_expr(expr)?;
            self.push_stmt(span, mir::StmtKind::Drop(place));
            Ok(())
        } else {
            self.error(errors::DroppedNonVariable { span })
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
                return self.error(errors::InferenceFailure {
                    span: lhs_span,
                    name: lhs_data,
                })
            }
            (Some(ty), _) => self.resolve_annot(ty)?,
            (_, Some(rhs)) => self.type_inner(rhs)?,
        };
        let place = self.gr.user_place(ty);
        if let Some(rhs) = rhs {
            self.lower_into(&place, rhs)?;
        }
        // NOTE It’s unfortunate that there is no way to insert this binding
        // *before* types are resolved. This can create a spurioius "unbound
        // name" error for each reference to a variable whose declaration is
        // broken.
        self.st.insert(lhs_data, place.root);
        Ok(())
    }

    /// Resolve a function from a local name
    fn resolve_function(&self, func: &SymbolId) -> Option<FnId> {
        let tab = &self.tables[self.table];
        tab.get_func(func, self.tables).map(|(fn_id, _)| *fn_id)
    }

    /// Resolve a type from a local name
    fn resolve_type(&self, ty: &SymbolId) -> Option<TyId> {
        let tab = &self.tables[self.table];
        tab.get_udt(ty, self.tables)
            .map(|(udt, _)| self.udt_tys.get(udt))
            .flatten()
            .copied()
    }

    // FIXME this convenience method just wraps `typing::resolve_annot` to supply
    // its bevy of arguments.
    fn resolve_annot(&mut self, ty: &Annot) -> Maybe<TyId> {
        typing::resolve_annot(
            ty,
            &self.tables[self.table],
            &self.tables,
            &self.udt_tys,
            &mut self.errors,
            &mut self.ctx,
        )
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
    use crate::index_type;

    pub fn resolve_ref_annot(annot: &RefAnnot) -> RefKind {
        match annot.kind {
            RefAnnotKind::Shrd => RefKind::Shrd,
            RefAnnotKind::Uniq => RefKind::Uniq,
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
                ExprKind::Assn { op, lhs, rhs } => self.type_assn(op, lhs, rhs)?,
                ExprKind::Literal(lit) => self.type_literal(lit),
                ExprKind::Ident(ident) => self.type_ident(ident)?,
                ExprKind::Field(root, field) => self.type_field(root, field)?,
                ExprKind::Tuple(elems) => self.type_tuple(elems)?,
                ExprKind::Struct { ty, fields } => self.type_struct(ty, fields)?,
                ExprKind::IntArr { item, reps } => self.type_int_arr(item, reps)?,
                ExprKind::ExtArr(elems) => self.type_ext_arr(elems)?,
                ExprKind::Block(block) => self.type_block(block)?,
                ExprKind::If {
                    cond,
                    tru: dir,
                    fls: ind,
                } => self.type_if(cond, dir, ind)?,
                ExprKind::Match { scr, arms } => self.type_match(scr, arms)?,
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
                ExprKind::Ref { annot, expr } => {
                    let kind = resolve_ref_annot(annot);
                    let ty = self.type_expr(expr)?;
                    self.ctx.intern_ty(Type::Ref(kind, ty))
                }
                ExprKind::Deref(expr) => {
                    let ty = self.type_expr(expr)?;
                    match self.ctx.types[ty] {
                        Type::Ref(_, ty) => ty,
                        _ => {
                            return self.error(errors::NonDereferenceableType {
                                span: expr.span,
                                ty,
                            })
                        }
                    }
                }
            };
            self.gamma.insert(expr.node, ty);
            Ok(ty)
        }

        pub fn type_field(&mut self, root: &Expr, field: &Field) -> Maybe<TyId> {
            let root = self.type_expr(root)?;
            match self.field_of(root, field) {
                Some((_, ty)) => Ok(ty),
                None => Err(self.errors.push(errors::NoSuchField {
                    span: field.span,
                    ty: root,
                    field: field.data.clone(),
                })),
            }
        }

        /// Resolves a field to its index position and type, if it exists
        pub fn field_of(&self, root: TyId, field: &Field) -> Option<(usize, TyId)> {
            match (&self.ctx.types[root], &field.data) {
                (Type::Tuple(tys), FieldKind::Num(n)) => {
                    let n = *n as usize;
                    if n < tys.len() {
                        Some((n, tys[n]))
                    } else {
                        None
                    }
                }
                (Type::UserType(udt), FieldKind::Ident(ident)) => {
                    // NOTE This is an O(n) lookup. Maybe we should store both the
                    // Vec of fields (for ordering) and the hashmap (for random
                    // lookup) in the udt.
                    udt.fields.iter().enumerate().find_map(|(n, (field, ty))| {
                        if field == ident {
                            Some((n, *ty))
                        } else {
                            None
                        }
                    })
                }
                _ => None,
            }
        }

        fn type_binop(&mut self, left: &Expr, op: &ast::BinOp, right: &Expr) -> Maybe<TyId> {
            use BinOpKind::*;
            use RefKind::*;
            let left = self.type_inner(left)?;
            let right = self.type_inner(right)?;

            match &op.data {
                Equal | Nequal => {
                    let lty = &self.ctx.types[left];
                    let rty = &self.ctx.types[left];
                    match (lty, rty) {
                        (Type::Ref(Shrd, _), Type::Ref(Shrd, _)) => {
                            if left == right && !left.is_classical(self.ctx) {
                                return Ok(left);
                            }
                        }
                        _ => {
                            if left == right && left.is_classical(self.ctx) {
                                return Ok(self.ctx.common.bool);
                            } else {
                                ()
                            }
                        }
                    }
                }
                DotDot => todo!(),
                Plus | Times => {
                    if (left == right) & left.is_uint(&self.ctx) {
                        return Ok(left);
                    }
                }
                Minus => todo!(),
                Mod => todo!(),
                Less => todo!(),
                Greater => todo!(),
                Swap => {
                    if let Some(Uniq) = left.ref_kind(&self.ctx) {
                        if left == right {
                            return Ok(self.ctx.common.unit);
                        }
                    }
                }
                And | Or | Xor => {
                    use RefKind::*;
                    let lty = &self.ctx.types[left];
                    let rty = &self.ctx.types[left];
                    match (lty, rty) {
                        (Type::Ref(Shrd, lty), Type::Ref(Shrd, rty)) => {
                            if rty == rty && *lty == self.ctx.common.q_bool {
                                return Ok(left);
                            }
                        }
                        (Type::Bool, Type::Bool) => return Ok(self.ctx.common.bool),
                        _ => (),
                    }
                }
            };
            Err(self.errors.push(errors::BinOpTypeError {
                span: op.span,
                kind: op.data,
                left,
                right,
            }))
        }

        fn type_unop(&mut self, op: &ast::UnOp, right: &Expr) -> Maybe<TyId> {
            let right = self.type_inner(right)?;
            match &op.data {
                UnOpKind::Minus => todo!(),
                UnOpKind::Not => {
                    if [
                        self.ctx.common.bool,
                        self.ctx.common.q_bool,
                        self.ctx.common.shrd_q_bool,
                    ]
                    .contains(&right)
                    {
                        Ok(right)
                    } else {
                        Err(self.errors.push(errors::UnOpOutTypeError {
                            span: op.span,
                            kind: op.data,
                            ty: right,
                        }))
                    }
                }
                UnOpKind::Split => {
                    if right.is_primitive(self.ctx) & right.is_coherent(self.ctx) {
                        Ok(right)
                    } else {
                        Err(self.errors.push(errors::UnOpOutTypeError {
                            span: op.span,
                            kind: op.data,
                            ty: right,
                        }))
                    }
                }
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

        fn type_assn(&mut self, op: &AssnOp, lhs: &Expr, rhs: &Expr) -> Maybe<TyId> {
            // NOTE: Check the lhs and rhs, to make sure validations happen. But, this
            // is not where the *equality of the sides* is checked: that is at
            // the top of `lower_into`.
            //
            // Why is that?
            let lty = self.type_expr(lhs)?;
            let rty = self.type_expr(rhs)?;
            let well_typed = match op.data {
                AssnOpKind::Equal => true, // as per the magic comment, do nothing
                AssnOpKind::And | AssnOpKind::Or => lty == rty && lty.is_classical(self.ctx),
                AssnOpKind::Xor => {
                    if lty.is_classical(self.ctx) {
                        lty == rty
                    } else {
                        if let Type::Ref(RefKind::Shrd, rty_inner) = self.ctx.types[rty] {
                            lty == rty_inner
                        } else {
                            false
                        }
                    }
                }
            };
            if well_typed {
                Ok(self.ctx.common.unit)
            } else {
                Err(self.errors.push(errors::AssnOpTypeError {
                    span: op.span,
                    kind: op.data,
                    rty,
                    lty,
                }))
            }
        }

        fn type_literal(&mut self, lit: &Literal) -> TyId {
            match &lit.data {
                LiteralKind::True => self.ctx.common.bool,
                LiteralKind::False => self.ctx.common.bool,
                LiteralKind::Nat(_, Some(Uint::U2)) => todo!(),
                LiteralKind::Nat(_, Some(Uint::U4)) => self.ctx.common.u4,
                LiteralKind::Nat(_, Some(Uint::U8)) => self.ctx.common.u8,
                LiteralKind::Nat(_, Some(Uint::U16)) => self.ctx.common.u16,
                LiteralKind::Nat(_, Some(Uint::U32)) => self.ctx.common.u32,
                LiteralKind::Nat(_, None) => self.ctx.common.u32,
                LiteralKind::Ord => self.ctx.common.ord,
            }
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

        fn type_match(&mut self, _scr: &Expr, _arms: &[MatchArm]) -> Maybe<TyId> {
            todo!()
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
            let ty = self.ctx.intern_ty(Type::Tuple(tys));
            Ok(ty)
        }

        fn type_struct(&mut self, name: &Ident, fields: &[(Ident, Expr)]) -> Maybe<TyId> {
            let ty = match self.resolve_type(&name.data) {
                Some(ty) => ty,
                None => {
                    return Err(self.errors.push(errors::NoSuchType {
                        span: name.span,
                        name: name.data,
                    }))
                }
            };

            let udt = match &self.ctx.types[ty] {
                Type::UserType(udt) => udt,
                _ => unreachable!(),
            };

            // Now we want to check that the fields all have the right names and
            // types. The crux here is an efficient symmetric set difference,
            // which isn't all that hard, but you've got to do it.

            // First, compare everything in the received fields to the expected
            // fields.
            //
            // FIXME For now we'll collect the expected fields in a hashset
            // here, but this will do many more allocations than necessary and
            // recompute this set many times. It should be stored with the
            // data structure itself.
            let expected: HashMap<SymbolId, TyId> =
                udt.fields.iter().map(|(s, t)| (*s, *t)).collect();
            for (name, _) in fields.iter() {
                match expected.get(&name.data) {
                    // Don't need to check here if if a field's type is actually
                    // correct! That will be happen when lowering the field.
                    Some(_) => {}
                    None => {
                        return Err(self.errors.push(errors::NoSuchField {
                            span: name.span,
                            ty,
                            field: name.data.into(),
                        }))
                    }
                };
            }

            // Now we should go the other way, doing the same thing. But! This
            // would mean allocating for another `HashMap`. In fact, we'll be
            // doing that *anyway* in the method `lower_into_struct`. So we've
            // put that half of the set difference up there, at the cost of
            // making this code a little more spagghetified.

            Ok(ty)
        }

        fn type_int_arr(&mut self, _item: &Expr, _reps: &Expr) -> Maybe<TyId> {
            todo!()
        }

        fn type_ext_arr(&mut self, elems: &[Expr]) -> Maybe<TyId> {
            let mut elems = elems.iter();
            let fst = match elems.next().and_then(|head| Some(self.type_expr(head))) {
                Some(ty) => ty?,
                None => todo!(),
            };

            let incorrect_tys = elems
                .map(|elem| self.type_expr(elem))
                .filter(|elem| elem != &Ok(fst));

            for _ty in incorrect_tys {
                todo!();
            }

            Ok(fst)
        }
    }

    /*
    FIXME This type signature is *ridiculous*. There's a lot of context
    (including a `Context`) explicitly passed in. We need a table. `errs` is
    an error buffer passed in in order to be able to get 'no-such-types
    errors out. So, why not make this function a method of `MirBuilder` or
    `GraphBuilder`? Well, because it has to be used by both of them! If
    there's a better way to make it available to both, and have a simpler
    signature, I'd love to know it.

    Come to think of it, this bit of ugliness could be cleaned up by using
    another IR between the AST and MIR, mut like Rust does, in which names
    and types are all resolved, but no further lowering has taken place.
    */

    /// Resolve an annotation to a type, given a table (scope) in which it
    /// should appear. This should eventually be farmed out to a type inference
    /// module/crate, and/or appear earlier in the compilaton process. For now
    /// it doesn't hurt to include here.
    pub fn resolve_annot(
        annot: &Annot,
        tab: &Table,
        tables: &TableStore,
        udt_tys: &HashMap<UdtId, TyId>,
        errs: &mut ErrorBuf,
        ctx: &mut Context,
    ) -> Maybe<TyId> {
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
                    .map(|ann| resolve_annot(ann, tab, tables, udt_tys, errs, ctx))
                    .collect::<Maybe<Vec<TyId>>>()?;
                ctx.intern_ty(Type::Tuple(inner_types))
            }
            AnnotKind::Array(inner) => {
                let inner = resolve_annot(inner, tab, tables, udt_tys, errs, ctx)?;
                ctx.intern_ty(Type::Array(inner))
            }
            AnnotKind::Question(inner) => {
                let ty = resolve_annot(inner, tab, tables, udt_tys, errs, ctx)?;
                resolve_annot_question(ctx, ty)?
            }
            AnnotKind::Bang(inner) => {
                let ty = resolve_annot(inner, tab, tables, udt_tys, errs, ctx)?;
                resolve_annot_bang(ctx, ty)?
            }
            AnnotKind::Ident(ident) => match tab.get_udt(&ident.data, tables) {
                Some((udt_id, _)) => *udt_tys.get(udt_id).unwrap(),
                None => {
                    return Err(errs.push(errors::NoSuchType {
                        span: ident.span,
                        name: ident.data,
                    }));
                }
            },
            AnnotKind::Func(params, ret) => {
                let param_tys = params
                    .iter()
                    .map(|ann| resolve_annot(ann, tab, tables, udt_tys, errs, ctx))
                    .collect::<Maybe<Vec<TyId>>>()?;
                let ret_ty = match ret {
                    Some(ret) => resolve_annot(ret, tab, tables, udt_tys, errs, ctx)?,
                    None => ctx.common.unit,
                };
                ctx.intern_ty(Type::Func(param_tys, ret_ty))
            }
            AnnotKind::Ref(annot, inner) => {
                let ty = resolve_annot(inner, tab, tables, udt_tys, errs, ctx)?;
                let kind = resolve_ref_annot(annot);
                ctx.intern_ty(Type::Ref(kind, ty))
            }
            AnnotKind::Ord => ctx.common.ord,
        };

        Ok(ty)
    }

    // Can remove this attribute after implementing the rest of the function
    #[allow(clippy::unnecessary_wraps)]
    fn resolve_annot_question(ctx: &mut Context, inner: TyId) -> Maybe<TyId> {
        use Type::*;
        // can this be done with just pointer comparisons?
        let ty = match ctx.types[inner] {
            Bool => Q_Bool,
            Uint(u) => Q_Uint(u),
            _ => todo!(),
        };
        Ok(ctx.intern_ty(ty))
    }

    // Can remove this attribute after implementing the rest of the function
    #[allow(clippy::unnecessary_wraps)]
    fn resolve_annot_bang(ctx: &mut Context, inner: TyId) -> Maybe<TyId> {
        use Type::*;
        // can this be done with just pointer comparisons?
        let ty = match ctx.types[inner] {
            Q_Bool => Bool,
            Q_Uint(u) => Uint(u),
            _ => todo!(),
        };
        Ok(ctx.intern_ty(ty))
    }
}

/// Some module-local utility functions
mod util {
    /// Get the number of bits to specify an element in a set of size `n`.
    pub fn bitsize(n: usize) -> usize {
        let mut mask = usize::MAX;
        // to be the first place-value at which the mask no longer overlaps
        let mut place: usize = 0;
        while (n.saturating_sub(1) & mask) != 0 {
            mask = mask << 1;
            place += 1;
        }
        //place.saturating_sub(1)
        place
    }

    #[test]
    fn bitsize_correct() {
        assert_eq!(bitsize(0), 0);
        assert_eq!(bitsize(1), 0);
        assert_eq!(bitsize(2), 1);
        assert_eq!(bitsize(3), 2);
        assert_eq!(bitsize(4), 2);
        assert_eq!(bitsize(5), 3);
    }
}

mod errors {
    use crate::ast::*;
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
    #[msg = "assignment operator `{kind}` doesn't support types `{lty}` and `{rty}`"]
    pub struct AssnOpTypeError {
        #[span]
        pub span: Span,
        pub kind: AssnOpKind,
        #[ctx]
        pub rty: TyId,
        #[ctx]
        pub lty: TyId,
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
    #[msg = "name `{name}` cannot be found in this scope"]
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
        #[span(msg = "expected an lvalue here")]
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

    #[derive(Diagnostic)]
    #[msg = "attempted to access field `{attempt}` of a tuple that only has {len} factors"]
    pub struct TupleOutOfBounds {
        #[span]
        pub span: Span,
        pub len: usize,
        pub attempt: usize,
    }

    #[derive(Diagnostic)]
    #[msg = "the type `{ty}` has no field `{field}`"]
    pub struct NoSuchField {
        #[span]
        pub span: Span,
        #[ctx]
        pub ty: TyId,
        #[ctx]
        pub field: FieldKind,
    }

    #[derive(Diagnostic)]
    #[msg = "missing initializer for the field `{field}` of `{name}`"]
    pub struct MissingStructField {
        #[span]
        pub span: Span,
        #[ctx]
        pub name: SymbolId,
        #[ctx]
        pub field: SymbolId,
    }

    #[derive(Diagnostic)]
    #[msg = "type `{name}` cannot be found in this scope"]
    pub struct NoSuchType {
        #[span]
        pub span: Span,
        #[ctx]
        pub name: SymbolId,
    }

    #[derive(Diagnostic)]
    #[msg = "cannot dereference values of type `{ty}`"]
    pub struct NonDereferenceableType {
        #[span]
        pub span: Span,
        #[ctx]
        pub ty: TyId,
    }

    #[derive(Diagnostic)]
    #[msg = "explicit lifetime `'{name}` forbidden in borrow expression"]
    pub struct LifetimeInBorrow {
        #[span]
        pub span: Span,
        #[ctx]
        pub name: SymbolId,
    }

    #[derive(Diagnostic)]
    #[msg = "`drop` statements can only take variables and paths"]
    pub struct DroppedNonVariable {
        #[span]
        #[msg = "must be of the form `x`, or `y.0.a`"]
        pub span: Span,
    }
}
