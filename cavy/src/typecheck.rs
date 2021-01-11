use crate::ast::*;
use crate::cavy_errors::{CavyError, Diagnostic, ErrorBuf, Result};
// use crate::functions::{Func, UserFunc};
use crate::session::Session;
use crate::types::{TyId, TyStore, Type};
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// Main entry point for the semantic analysis phase.
///
/// Run a type-checking pass, annotating the AST as you go, and return a valid
/// symbol table. For now, this is the single entry point for all semantic
/// analysis passes, not just type-checking proper. It will also mutate the AST,
/// adding type annotations where necessary (or possible).
pub fn typecheck<'ctx>(
    ctx: &'ctx AstCtx,
    sess: &'ctx Session,
) -> std::result::Result<(), ErrorBuf> {
    let tc = Typechecker::new(ctx, sess);
    tc.typecheck()
}

/// A `typing context`. Unlike the similarly-named data structure in `rustc`,
/// this doesn't do double duty--it's exactly what it says on the tin.
pub struct TyCtx {
    /// Types of functions
    funcs: HashMap<FnId, TyId>,
    /// The backing type store
    types: TyStore,
}

/// This struct handles essentially all of the semantic analysis passes; the
/// name might be a little misleading. However, its main job is to produce a
/// well-typed symbol table.
pub struct Typechecker<'ctx> {
    ctx: &'ctx AstCtx,
    sess: &'ctx Session,
    pub errors: ErrorBuf,
}

impl<'ctx> Typechecker<'ctx> {
    pub fn new(ctx: &'ctx AstCtx, sess: &'ctx Session) -> Self {
        Self {
            ctx,
            sess,
            errors: ErrorBuf::new(),
        }
    }

    /// Typecheck all funcitons in the AST
    pub fn typecheck(self) -> std::result::Result<(), ErrorBuf> {
        // todo!();
        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }

    pub fn type_fn(&self, fn_id: FnId) -> Result<()> {
        let func = &self.ctx.funcs[fn_id];
        let body = &self.ctx.bodies[func.body];
        let ty = self.type_expr(body);
        // compare ty to func's return value
        Ok(())
    }

    pub fn type_expr(&self, expr: &Expr) -> Result<()> {
        todo!()
    }

    // /// Check the structural properties of each type
    // #[rustfmt::skip]
    // fn discipline(&self) -> StructuralDiscipline {
    //     use Type::*;
    //     match self {
    //         Bool =>            StructuralDiscipline { linear: false },
    //         U8 =>              StructuralDiscipline { linear: false },
    //         U16 =>             StructuralDiscipline { linear: false },
    //         U32 =>             StructuralDiscipline { linear: false },

    //         Q_Bool =>          StructuralDiscipline { linear: true },
    //         Q_U8 =>            StructuralDiscipline { linear: true },
    //         Q_U16 =>           StructuralDiscipline { linear: true },
    //         Q_U32 =>           StructuralDiscipline { linear: true },

    //         Array(ty) =>      ty.discipline(),

    //         // Tuples and structs are as constrained as their most constrained member
    //         Tuple(types) =>    StructuralDiscipline {
    //             linear: types.iter().any(|val| val.discipline().linear),
    //         },
    //         Measured(_) =>     StructuralDiscipline { linear: false },
    //     }
    // }

    // /// Check if the type is linear
    // pub fn is_linear(&self) -> bool {
    //     self.discipline().linear
    // }

    // /// Typecheck a statement. This will be executed after hoisting, so all items
    // /// will have been hoisted to the top.
    // pub fn type_stmt<'ast>(
    //     &mut self,
    //     stmt: &'ast Stmt,
    //     table: &mut SymbolTable<'ast>,
    // ) -> Result<()> {
    //     use StmtKind::*;
    //     match &stmt.kind {
    //         // No-op
    //         Print(_expr) => Ok(()),
    //         // An expression statement not decorated with a semicolon: could be a
    //         // return value from a block.
    //         Expr(expr) => self.type_expr(expr, table).map(|_| ()),
    //         // An expression statement decorated with a semicolon
    //         ExprSemi(expr) => self.type_expr(expr, table).map(|_| ()),
    //         // A new local binding: insert the name into the symbol table
    //         Local { lhs, ty, rhs } => {
    //             let ty = self.type_local(ty, rhs, table)?;
    //             self.insert_local(lhs, ty, table)?;
    //             Ok(())
    //         }
    //         // All these are expected to be at the top of the AST, as they’ve
    //         // already been hoisted.
    //         Item(item) => {
    //             table.insert_item(item);
    //             Ok(())
    //         }
    //     }
    // }

    // /// Typecheck a single expression
    // fn type_expr(&mut self, expr: &Expr, table: &SymbolTable) -> Result<Type> {
    //     match &expr.kind {
    //         ExprKind::BinOp { left, op, right } => self.type_binop(left, op, right, table),
    //         ExprKind::UnOp { op, right } => self.type_unop(op, right, table),
    //         ExprKind::Literal(lit) => self.type_literal(lit, table),
    //         ExprKind::Tuple(vals) => self.type_tuple(vals, table),
    //         // There is some duplication following us around here--perhaps we
    //         // ought to lower the representation somewhat.
    //         ExprKind::ExtArr(vals) => self.type_ext_arr(vals, table),
    //         ExprKind::IntArr { item, reps } => self.type_int_arr(item, reps, table),
    //         ExprKind::Ident(ident) => self.type_ident(ident, table),
    //         _ => todo!(),
    //     }
    // }

    // fn type_binop(
    //     &mut self,
    //     left: &Box<Expr>,
    //     op: &BinOp,
    //     right: &Box<Expr>,
    //     table: &SymbolTable,
    // ) -> Result<Type> {
    //     use BinOpKind::*;
    //     use Type::*;
    //     let ty_l = self.type_expr(left, table)?;
    //     let ty_r = self.type_expr(right, table)?;
    //     let ty = match (op.kind, ty_l, ty_r) {
    //         // These are not quite right!
    //         (Equal, l, r) if l == r => l,
    //         (Nequal, l, r) if l == r => l,

    //         (Plus, U8, U8) => U8,
    //         (Plus, U16, U16) => U16,
    //         (Plus, U32, U32) => U32,

    //         (Plus, Q_U8, Q_U8) => U8,
    //         (Plus, Q_U16, Q_U16) => U16,
    //         (Plus, Q_U32, Q_U32) => U32,

    //         (kind, left, right) => {
    //             return Err(self.errors.push(errors::BinOpTypeError {
    //                 span: op.span,
    //                 kind,
    //                 left,
    //                 right,
    //             }));
    //         }
    //     };
    //     Ok(ty)
    // }

    // fn type_unop(&mut self, op: &UnOp, right: &Box<Expr>, table: &SymbolTable) -> Result<Type> {
    //     use Type::*;
    //     use UnOpKind::*;
    //     let ty_r = self.type_expr(right, table)?;
    //     let ty = match (op.kind, ty_r) {
    //         (Minus, _) => unimplemented!(),

    //         (Not, Bool) => Bool,
    //         (Not, Q_Bool) => Bool,

    //         (Linear, Bool) => Q_Bool,
    //         (Linear, U8) => Q_U8,
    //         (Linear, U16) => Q_U16,
    //         (Linear, U32) => Q_U32,

    //         (Delin, Q_Bool) => Bool,
    //         (Delin, Q_U8) => U8,
    //         (Delin, Q_U16) => U16,
    //         (Delin, Q_U32) => U32,

    //         (kind, right) => {
    //             return Err(self.errors.push(errors::UnOpTypeError {
    //                 span: op.span,
    //                 kind,
    //                 right,
    //             }));
    //         }
    //     };
    //     Ok(ty)
    // }

    // fn type_tuple(&mut self, vals: &Vec<Expr>, table: &SymbolTable) -> Result<Type> {
    //     let tys = vals
    //         .iter()
    //         .map(|v| self.type_expr(v, table))
    //         // NOTE: this short-circuits at the first error, which is really not
    //         // quite the behavior I want.
    //         .collect::<Result<Vec<Type>>>()?;
    //     Ok(Type::Tuple(tys))
    // }

    // fn type_ext_arr(&mut self, vals: &Vec<Expr>, table: &SymbolTable) -> Result<Type> {
    //     if vals.is_empty() {
    //         // This might have to wait for type inference to make sense.
    //         todo!();
    //     }

    //     let mut vals = vals.iter();
    //     // Unwrap safe because `vals` is known not to be empty.
    //     let ty = self.type_expr(vals.next().unwrap(), table)?;
    //     for v in vals {
    //         if self.type_expr(v, table)? != ty {
    //             return Err(self
    //                 .errors
    //                 .push(errors::HeterogeneousArray { span: v.span, ty }))?;
    //         }
    //     }

    //     Ok(Type::Array(Box::new(ty)))
    // }

    // fn type_int_arr(&mut self, item: &Expr, reps: &Expr, table: &SymbolTable) -> Result<Type> {
    //     let ty_item = self.type_expr(item, table)?;
    //     let ty_reps = self.type_expr(item, table)?;

    //     if ty_reps != Type::size_type() {
    //         return Err(self.errors.push(errors::ExpectedSizeType {
    //             span: reps.span,
    //             ty: ty_reps,
    //         }))?;
    //     }

    //     Ok(Type::Array(Box::new(ty_item)))
    // }

    // fn type_local(&mut self, _ty: &Option<Annot>, rhs: &Expr, table: &SymbolTable) -> Result<Type> {
    //     let ty_r = self.type_expr(rhs, table)?;
    //     Ok(ty_r)
    // }

    // fn resolve_annot(&self, annot: &Annot, table: &SymbolTable) -> Result<Type> {
    //     let ty = match &annot.kind {
    //         AnnotKind::Bool => Type::Bool,
    //         AnnotKind::U8 => Type::U8,
    //         AnnotKind::U16 => Type::U16,
    //         AnnotKind::U32 => Type::U32,

    //         AnnotKind::Tuple(inners) => {
    //             let inner_types = inners
    //                 .iter()
    //                 .map(|ann| self.resolve_annot(ann, table))
    //                 .collect::<Result<Vec<Type>>>()?;
    //             Type::Tuple(inner_types)
    //         }
    //         AnnotKind::Array(inner) => {
    //             let ty = Box::new(self.resolve_annot(inner, table)?);
    //             Type::Array(ty)
    //         }

    //         AnnotKind::Question(inner) => {
    //             let ty = self.resolve_annot(inner, table)?;
    //             self.resolve_annot_question(ty, table)?
    //         }

    //         AnnotKind::Bang(inner) => {
    //             let ty = self.resolve_annot(inner, table)?;
    //             self.resolve_annot_bang(ty)?
    //         }

    //         AnnotKind::Ident(_ident) => {
    //             todo!()
    //         }
    //     };

    //     Ok(ty)
    // }

    // fn type_literal(&mut self, lit: &Literal, _table: &SymbolTable) -> Result<Type> {
    //     use LiteralKind::*;
    //     use Type::*;
    //     match lit.kind {
    //         True => Ok(Bool),
    //         False => Ok(Bool),
    //         Nat(_) => Ok(U32),
    //     }
    // }

    // fn type_ident(&mut self, ident: &Ident, table: &SymbolTable) -> Result<Type> {
    //     // NOTE: cann’t use `ok_or` here because it evaluates its arguments
    //     // eagerly.
    //     let symb = table.get(&ident).ok_or_else(|| {
    //         self.errors.push(errors::UnboundName {
    //             span: ident.span,
    //             name: ident.name.clone(),
    //         })
    //     });

    //     match symb {
    //         // This clone is not wasted--we might well need to make a new symbol
    //         // that has the same type!
    //         Ok(symb) => Ok(symb.ty.clone()),
    //         Err(err) => Err(err),
    //     }
    // }

    // fn resolve_annot_question(&self, inner: Type, _table: &SymbolTable) -> Result<Type> {
    //     let ty = match inner {
    //         Type::Bool => Type::Q_Bool,
    //         Type::U8 => Type::Q_U8,
    //         Type::U16 => Type::Q_U16,
    //         Type::U32 => Type::Q_U32,

    //         _ => unimplemented!(),
    //     };
    //     Ok(ty)
    // }

    // fn resolve_annot_bang(&self, inner: Type) -> Result<Type> {
    //     let ty = match inner {
    //         Type::Q_Bool => Type::Bool,
    //         Type::Q_U8 => Type::U8,
    //         Type::Q_U16 => Type::U16,
    //         Type::Q_U32 => Type::U32,

    //         _ => unimplemented!(),
    //     };
    //     Ok(ty)
    // }

    // /// Insert local bindings, recursively destructuring the LValue and type
    // fn insert_local<'ast>(
    //     &mut self,
    //     lhs: &'ast LValue,
    //     ty: Type,
    //     table: &mut SymbolTable<'ast>,
    // ) -> Result<()> {
    //     match (&lhs.kind, ty) {
    //         (LValueKind::Tuple(lvalues), Type::Tuple(tys)) => {
    //             if lvalues.len() != tys.len() {
    //                 return Err(self.errors.push(errors::DestructuringError {
    //                     span: lhs.span,
    //                     // Have to rebuild the type because it was moved in here
    //                     actual: Type::Tuple(tys),
    //                 }))?;
    //             }

    //             for (lvalue, ty) in lvalues.iter().zip(tys.into_iter()) {
    //                 self.insert_local(lvalue, ty, table)?;
    //             }
    //         }

    //         (LValueKind::Ident(ident), ty) => match table.insert_var(ident, ty) {
    //             None => {}
    //             // TODO report some information about the contained symbol
    //             Some(_) => {
    //                 return Err(self.errors.push(errors::NameCollision {
    //                     span: lhs.span,
    //                     name: ident.name.clone(),
    //                 }))?;
    //             }
    //         },

    //         // In all other cases, we've failed to destructure
    //         (_, ty) => {
    //             return Err(self.errors.push(errors::DestructuringError {
    //                 span: lhs.span,
    //                 // Have to rebuild the type because it was moved in here
    //                 actual: ty,
    //             }))?;
    //         }
    //     };
    //     Ok(())
    // }
}

// /// Hoists `fn`, `struct`, `enum` declarations to the top of a list of
// /// statements, but does not insert them in a symbol table.
// pub fn hoist_items(stmts: &mut Vec<Stmt>) {
//     // `Vec::sort_by` is a stable sort, so all this will do is carry items to
//     // the top, without reordering anything else. This significantly simplifies
//     // the implementation, at least as long as `drain_filter` is unstable.
//     stmts.sort_by(|left, right| {
//         let left = left.kind.is_item();
//         let right = right.kind.is_item();
//         left.cmp(&right)
//     });
// }

// /// Lives in symbol table; carries type, lifetime information and so on.
// #[derive(Debug)]
// pub struct Symbol {
//     kind: SymbolKind,
//     ty: Type,
// }
//
// #[derive(Debug)]
// pub enum SymbolKind {
//     Fn(Box<dyn Func>),
//     Var,
// }
//
// #[derive(Debug)]
// pub struct SymbolTable<'ast> {
//     /// For now, there is a single namespace for all symbols. It might be better
//     /// to have separate namespaces for functions, variables, types, and so on.
//     symbols: HashMap<&'ast str, Symbol>,
//     parent: Option<Weak<SymbolTable<'ast>>>,
// }
//
// impl<'ast> SymbolTable<'ast> {
//     pub fn new() -> Self {
//         Self {
//             symbols: HashMap::new(),
//             parent: None,
//         }
//     }
//
//     fn insert_item(&mut self, item: &'ast Item) {
//         match &item.kind {
//             ItemKind::Fn {
//                 name,
//                 params: _,
//                 typ: _,
//                 body,
//                 docstring,
//             } => {
//                 let func = Box::new(UserFunc {
//                     params: vec![],
//                     // FIXME temporarily defeating the borrow checker
//                     body: body.clone(),
//                     doc: docstring.clone(),
//                 });
//                 let symb = Symbol {
//                     ty: Type::unit(),
//                     kind: SymbolKind::Fn(func),
//                 };
//                 self.symbols.insert(&name.name, symb);
//             }
//         }
//     }
//
//     fn insert_var(&mut self, ident: &'ast Ident, ty: Type) -> Option<Symbol> {
//         let symb = Symbol {
//             kind: SymbolKind::Var,
//             ty,
//         };
//         let symb = self.symbols.insert(&ident.name, symb);
//         symb
//     }
//
//     fn get(&self, ident: &'ast Ident) -> Option<&Symbol> {
//         self.symbols.get(ident.name.as_str())
//     }
// }

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
