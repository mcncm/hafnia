//! The highest-level representation of the Cavy program. This is not exactly a
//! pure parse tree; it is already somewhat lowered, with symbols already
//! interned, functions and structs already hoisted, and a few basic
//! (lexically-checkable) invariants checked.
//!
//! The IRs (in `ast.rs` and `cfg.rs`) are, of course, very similar to those
//! found in rustc. `ast.rs` is somewhere in between that compiler's AST and
//! HIR, while the CFG is very similar to its MIR.

use crate::num::Uint;
use crate::source::Span;
use crate::token::{Token, Unsigned};
use crate::util::FmtWith;
use crate::{
    context::{Context, SymbolId},
    store::Counter,
};
use crate::{index_type, interner_type, store_type};
use std::convert::TryFrom;
use std::fmt;
use std::{collections::HashMap, ops::RangeFrom};

// Each of the AST items in this module is given as a wrapper struct (possibly
// with a single field) enclosing an internal enum listing the variants for
// that item. This pattern was borrowed from rustc itself, as I found that it
// resolved the problem of a proliferation of AST types for each semantic
// analysis pass.
store_type! { FnStore : FnId -> Func }
store_type! { BodyStore : BodyId -> Expr }
store_type! { UdtStore : UdtId -> Udt }
store_type! { TableStore : TableId -> Table }
index_type! { NodeId }

/// This data structure holds the AST-level symbol tables, etc., associated with
/// a single compilation unit. All the surrounding data structures used by
/// parsers go here. Note that this is conceptually similar to the
/// `rustc_hir::hir::Crate` struct in rustc.
#[derive(Debug, Default)]
pub struct Ast {
    /// Function items
    pub funcs: FnStore,
    /// Function bodies
    pub bodies: BodyStore,
    /// User-defined types
    pub udts: UdtStore,
    /// Symbol tables associated with scoped environments
    pub tables: TableStore,
    /// Node Id counter. This might not be necessary if we choose to put each
    /// node into a flat array ('store'), as we've done with the functions,
    /// function bodies and tables.
    pub counter: Counter<NodeId>,
    /// `main` function
    pub entry_point: Option<FnId>,
}

impl Ast {
    pub fn new() -> Self {
        Self::default()
    }

    /// Try to insert a function into a table.
    /// TODO make this a method of Table
    pub fn insert_fn(
        &mut self,
        tab: TableId,
        symb: SymbolId,
        span: Span,
        func: FnId,
    ) -> Option<(FnId, Span)> {
        self.tables[tab].funcs.insert(symb, (func, span))
    }

    /// Try to insert a user-defined type into a table.
    /// TODO ibid
    pub fn insert_udt(
        &mut self,
        tab: TableId,
        symb: SymbolId,
        span: Span,
        udt: UdtId,
    ) -> Option<(UdtId, Span)> {
        self.tables[tab].udts.insert(symb, (udt, span))
    }

    /// Create a new table without parent
    pub fn new_table(&mut self) -> TableId {
        self.tables.insert(Table::new())
    }

    /// Spawn a child and return its id
    pub fn child_table(&mut self, table: TableId) -> TableId {
        self.tables.insert(Table::child(table))
    }
}

/// A scoped symbol table containing descriptor references for items (functions,
/// types, and modules). This may correspond to a lexical block, module, or
/// function parameters. We should, however, consider splitting those up,
/// possibly using a separate type for function parameters.
#[derive(Debug, Default)]
pub struct Table {
    /// The enclosing scope, if there is any
    pub parent: Option<TableId>,
    /// Functions visible in this scope. While locals should also be able to
    /// "shadow" functions, and it will one day be possible to define lambda
    /// expressions, this table contains those functions defined with the `fn`
    /// keyword. They must be unique.
    ///
    /// Function ids are stored with their definition site.
    pub funcs: HashMap<SymbolId, (FnId, Span)>,
    /// User-defined types visible in this scope. User-defined type ids are
    /// stored with their definition site.
    pub udts: HashMap<SymbolId, (UdtId, Span)>,
}

impl Table {
    fn new() -> Self {
        Self::default()
    }

    fn child(table: TableId) -> Self {
        Table {
            parent: Some(table),
            funcs: HashMap::new(),
            udts: HashMap::new(),
        }
    }

    /// Abstracts over a recursive lookup associated with a symbol. The function
    /// pointer argument lets us use different strategies to return a function,
    /// type, or one or the other.
    fn get<'a, T, F>(
        &'a self,
        symb: &'a SymbolId,
        tables: &'a TableStore,
        // This argument instructs how to look up the reference within a single
        // table
        get_inner: F,
    ) -> Option<&'a T>
    where
        F: Fn(&'a Self, &'a SymbolId) -> Option<&'a T>,
    {
        match get_inner(self, &symb) {
            v @ Some(_) => v,
            None => match self.parent {
                Some(id) => {
                    let parent = &tables[id];
                    parent.get(symb, tables, get_inner)
                }
                None => None,
            },
        }
    }

    pub fn get_func<'a>(
        &'a self,
        symb: &'a SymbolId,
        tables: &'a TableStore,
    ) -> Option<&'a (FnId, Span)> {
        self.get(symb, tables, |this: &Self, symb| this.funcs.get(symb))
    }

    pub fn get_udt<'a>(
        &'a self,
        symb: &'a SymbolId,
        tables: &'a TableStore,
    ) -> Option<&'a (UdtId, Span)> {
        self.get(symb, tables, |this: &Self, symb| this.udts.get(symb))
    }
}

/// A generic type for some ast node that contains a single "thing.""
#[derive(Debug)]
pub struct Spanned<T> {
    pub data: T,
    pub span: Span,
}

impl<T> PartialEq for Spanned<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T> Eq for Spanned<T>
where
    T: Eq,
{
    fn assert_receiver_is_total_eq(&self) {}
}

impl<T> Clone for Spanned<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            span: self.span,
        }
    }
}

/// Interface for ast nodes that can be made from a single token. Returns
/// Err(()) when the received token can't be transformed as the requested node.
pub trait FromToken {
    #![allow(clippy::result_unit_err)]
    fn from_token(token: Token) -> Result<Self, ()>
    where
        Self: Sized;
}

/// A module. For now there's only one module per program.
/// Identifier node
pub type Ident = Spanned<SymbolId>;

impl FromToken for Ident {
    fn from_token(token: Token) -> Result<Self, ()> {
        use crate::token::Lexeme;
        match token.lexeme {
            Lexeme::Ident(data) => Ok(Self {
                data,
                span: token.span,
            }),
            _ => Err(()),
        }
    }
}

/// The kinds of field accesses, like `x.a` and `b.1`.
#[derive(Debug, Clone)]
pub enum FieldKind {
    Ident(SymbolId),
    Num(u32),
}

impl From<SymbolId> for FieldKind {
    fn from(s: SymbolId) -> Self {
        Self::Ident(s)
    }
}

// NOTE I'm not sure I really want to be implementing this on things in the AST,
// instead of *just* the lightweight ID types. However, this is useful for
// certain diagnostic messages (see `lowering::errors::NoSuchField`).
impl<'c> FmtWith<Context<'c>> for FieldKind {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FieldKind::Ident(ident) => write!(f, "{}", ident.fmt_with(ctx)),
            FieldKind::Num(n) => write!(f, "{}", n),
        }
    }
}

pub type Field = Spanned<FieldKind>;

/// a pattern, such as appears on the receiving side of a `let` statement, or in
/// a (yet unimplemented) match arm.
pub type Pattern = Spanned<PatternKind>;

/// Currently, the only kind of pattern is a bare local
#[derive(Debug, Clone)]
pub enum PatternKind {
    Ident(SymbolId),
}

impl From<Ident> for Pattern {
    fn from(ident: Ident) -> Self {
        Self {
            data: PatternKind::Ident(ident.data),
            span: ident.span,
        }
    }
}

/// Binary operator node
pub type BinOp = Spanned<BinOpKind>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpKind {
    Equal,
    Nequal,
    DotDot,
    Plus,
    Minus,
    Times,
    Mod,
    Less,
    Greater,
    Swap,
    And,
    Or,
    Xor,
}

impl FromToken for BinOp {
    fn from_token(token: Token) -> Result<Self, ()> {
        use crate::token::Lexeme;
        use BinOpKind::*;
        let kind = match token.lexeme {
            Lexeme::EqualEqual => Equal,
            Lexeme::TildeEqual => Nequal,
            Lexeme::DotDot => DotDot,
            Lexeme::Plus => Plus,
            Lexeme::Minus => Minus,
            Lexeme::Star => Times,
            Lexeme::Percent => Mod,
            Lexeme::LAngle => Less,
            Lexeme::RAngle => Greater,
            Lexeme::VertVert => Or,
            Lexeme::AmpAmp => And,
            Lexeme::Dollar => Swap,
            _ => {
                return Err(());
            }
        };
        Ok(BinOp {
            data: kind,
            span: token.span,
        })
    }
}

/// This is a little bit redunant, because we're going *back* (hopefully
/// losslessly) to the lexeme that we came from. Such is the cost of moving the
/// checks earlier
impl fmt::Display for BinOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::token::Lexeme::*;
        let repr = match self {
            Self::Equal => EqualEqual,
            Self::Nequal => TildeEqual,
            Self::DotDot => DotDot,
            Self::Plus => Plus,
            Self::Minus => Minus,
            Self::Times => Star,
            Self::Mod => Percent,
            Self::Less => LAngle,
            Self::Greater => RAngle,
            Self::Swap => Dollar,
            Self::And => AmpAmp,
            Self::Or => VertVert,
            Self::Xor => CarotEqual,
        };
        write!(f, "{}", repr)
    }
}

/// Assignment operator node
pub type AssnOp = Spanned<AssnOpKind>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssnOpKind {
    Equal,
    And,
    Or,
    Xor,
}

impl fmt::Display for AssnOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::token::Lexeme::*;
        let repr = match self {
            Self::Equal => Equal,
            Self::And => AmpEqual,
            Self::Or => VertEqual,
            Self::Xor => CarotEqual,
        };
        write!(f, "{}", repr)
    }
}

impl FromToken for AssnOp {
    fn from_token(token: Token) -> Result<Self, ()> {
        use crate::token::Lexeme;
        use AssnOpKind::*;
        let kind = match token.lexeme {
            Lexeme::Equal => Equal,
            Lexeme::AmpEqual => And,
            Lexeme::VertEqual => Or,
            Lexeme::CarotEqual => Xor,
            _ => {
                return Err(());
            }
        };
        Ok(AssnOp {
            data: kind,
            span: token.span,
        })
    }
}

/// Unary operator node
pub type UnOp = Spanned<UnOpKind>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOpKind {
    Minus,
    Not,
    Split, // #
    Linear,
    Delin,
}

impl FromToken for UnOp {
    fn from_token(token: Token) -> Result<Self, ()> {
        use crate::token::Lexeme::*;
        let kind = match token.lexeme {
            Minus => UnOpKind::Minus,
            Tilde => UnOpKind::Not,
            Octothorpe => UnOpKind::Split,
            Question => UnOpKind::Linear,
            Bang => UnOpKind::Delin,
            _ => {
                return Err(());
            }
        };
        Ok(UnOp {
            data: kind,
            span: token.span,
        })
    }
}

/// This is a little bit redunant, because we're going *back* (hopefully
/// losslessly) to the lexeme that we came from. Such is the cost of moving the
/// checks earlier
impl fmt::Display for UnOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::token::Lexeme::*;
        let repr = match self {
            Self::Minus => Minus,
            Self::Not => Tilde,
            Self::Split => Octothorpe,
            Self::Linear => Question,
            Self::Delin => Bang,
        };
        write!(f, "{}", repr)
    }
}

/// A literal AST node
pub type Literal = Spanned<LiteralKind>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiteralKind {
    True,
    False,
    /// A natural number literal consists of a number in the internal
    /// representation, together with an optional tag representing its size.
    Nat(Unsigned, Option<Uint>),
    /// A literal inhabitant of the provisional experimental type
    Ord,
}

impl FromToken for Literal {
    fn from_token(token: Token) -> Result<Self, ()> {
        use crate::token::Lexeme::*;
        let kind = match token.lexeme {
            Nat(n, sz) => LiteralKind::Nat(n, sz),
            True => LiteralKind::True,
            False => LiteralKind::False,
            Ord => LiteralKind::Ord,
            _ => {
                return Err(());
            }
        };
        Ok(Literal {
            data: kind,
            span: token.span,
        })
    }
}

/// Expression node.
#[derive(Debug, Clone)]
pub struct Expr {
    pub data: ExprKind,
    pub span: Span,
    pub node: NodeId,
}

/// A kind of expression node.
#[derive(Debug, Clone)]
pub enum ExprKind {
    BinOp {
        left: Box<Expr>,
        op: BinOp,
        right: Box<Expr>,
    },
    UnOp {
        op: UnOp,
        right: Box<Expr>,
    },
    /// Assignment, as `x = y;`
    Assn {
        /// Should *ideally* be a pattern rather than an expression, which would
        /// remove the need to check later that this is the right kind of
        /// expression. However, that would make parsing more difficult, so we
        /// won't do it for now.
        op: AssnOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Literal(Literal),
    /// Identifiers
    Ident(Ident),
    /// Sequences of the form `(1, 2, 3)`
    Tuple(Vec<Expr>),
    /// A literal struct, like `A { a: true, b: ?3u8 }`
    Struct {
        /// The type named at the head of the expression
        ty: Ident,
        fields: Vec<(Ident, Expr)>,
    },
    /// Intensional arrays of the form `[1; 4]`
    IntArr {
        item: Box<Expr>,
        reps: Box<Expr>,
    },
    /// A field access, like `x.a` or `y.0`
    Field(Box<Expr>, Field),
    /// Extensional arrays of the form `[1, 2, 3]`
    ExtArr(Vec<Expr>),
    Block(Box<Block>),
    If {
        cond: Box<Expr>,
        /// Truthy branch
        tru: Box<Block>,
        /// Falsy branch
        fls: Option<Box<Block>>,
    },
    Match {
        /// The match expression scrutinee
        scr: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    For {
        bind: Box<LValue>,
        iter: Box<Expr>,
        body: Box<Block>,
    },
    Call {
        // FIXME For the time being, functions are not values, so the callee is not an
        // expression, but just a name. Arguments should also be expressions,
        // but they are currently also just identifiers.
        callee: Ident,
        args: Vec<Expr>,
    },
    Index {
        head: Box<Expr>,
        index: Box<Expr>,
    },
    Ref {
        annot: RefAnnot,
        expr: Box<Expr>,
    },
}

impl ExprKind {
    /// Some expressions require semicolons when used in expression statements.
    pub fn requires_semicolon(&self) -> bool {
        use ExprKind::*;
        match self {
            BinOp { .. } => true,
            UnOp { .. } => true,
            Ref { .. } => true,
            Assn { .. } => true,
            Literal(_) => true,
            Ident(_) => true,
            Field { .. } => true,
            Tuple { .. } => true,
            Struct { .. } => true,
            IntArr { .. } => true,
            ExtArr(_) => true,
            Block(_) => false,
            If { .. } => false,
            Match { .. } => false,
            For { .. } => false,
            Call { .. } => true,
            Index { .. } => true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pat: Pattern,
    pub expr: Box<Expr>,
}

/// A brace-delimited code block
#[derive(Debug, Clone)]
pub struct Block {
    /// The statements contained in the block
    pub stmts: Vec<Stmt>,
    /// The terminal expression, if there is one
    pub expr: Option<Box<Expr>>,
    /// The id of the table containing item definitions in
    /// this block scope.
    pub table: TableId,
    pub is_unsafe: bool,
    pub span: Span,
}

/// Statement node.
pub type Stmt = Spanned<StmtKind>;

// A highly dubious impl
impl From<StmtKind> for Stmt {
    fn from(kind: StmtKind) -> Self {
        Self {
            data: kind,
            span: Span::default(),
        }
    }
}

/// A kind of statement: this division of kinds is basically taken from `rustc_ast`.
#[derive(Debug, Clone)]
pub enum StmtKind {
    /// An input/output statement
    Io(Box<IoStmtKind>),
    /// An assertion
    Assert(Box<Expr>),
    /// A drop statement,
    Drop(Box<Expr>),
    /// An expression without a semicolon.
    Expr(Box<Expr>),
    /// An expression with a semicolon.
    ExprSemi(Box<Expr>),
    /// A variable declaration.
    Decl {
        /// lvalues might not just be names! In particular, we would like to make
        /// destructuring possible. The same is true of other contexts in which
        /// lvalues appear, as in the bound expression in a for loop.
        ///
        /// For now, though, we're going to ignore that possibility, disable
        /// destructuring, and allow only a symbol on the lhs.
        lhs: Box<Pattern>,
        ty: Option<Annot>,
        rhs: Option<Box<Expr>>,
    },
}

#[derive(Debug, Clone)]
/// There are two kinds of runtime I/O, corresponding to sending messages in
/// (from the perspective of the coprocessor) and out (same).
pub enum IoStmtKind {
    /// in-I/O currently does nothing; there's no way for the parser to even
    /// construct it.
    In,
    Out {
        lhs: Box<Expr>,
        name: Ident,
    },
}

/// Something that can be assigned to
pub type LValue = Spanned<LValueKind>;

// Another dubious impl
impl From<LValueKind> for LValue {
    fn from(kind: LValueKind) -> Self {
        Self {
            data: kind,
            span: Span::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum LValueKind {
    /// A simple identifier
    Ident(Ident),
    /// Sequence of the form (a, b, c)
    Tuple(Vec<LValue>),
}

#[derive(Debug, Clone)]
pub enum RefAnnotKind {
    /// &
    Shrd,
    /// &mut
    Uniq,
}

/// A reference annotation like `& 'a` or `&mut`
#[derive(Debug, Clone)]
pub struct RefAnnot {
    pub kind: RefAnnotKind,
    pub lifetime: Option<Lifetime>,
    pub span: Span,
}

/// Type annotations. These are distinct from, and not convertible to types. The
/// reason is that there may be identical type annotations that resolve to
/// different types within different scopes because of user-defined structs and
/// type aliases.
pub type Annot = Spanned<AnnotKind>;

#[derive(Debug, Clone)]
pub enum AnnotKind {
    Bool,
    Uint(Uint),

    Tuple(Vec<Annot>),
    Array(Box<Annot>),

    /// Linearization of a type annotation: e.g. `?u8`
    Question(Box<Annot>),
    /// Delinearization of a type annotation: e.g. `!Cat`
    Bang(Box<Annot>),

    /// User-defined types
    Ident(Ident),

    /// Function types
    Func(Vec<Annot>, Option<Box<Annot>>),

    /// `&T` or `&mut T`
    Ref(RefAnnot, Box<Annot>),

    /// Provisional experimental type
    Ord,
}

/// A user-defined type
#[derive(Debug)]
pub struct Udt {
    /// The table in which this type is defined
    pub table: TableId,
    pub kind: UdtKind,
}

#[derive(Debug)]
pub enum UdtKind {
    Struct(Struct),
    Enum(Enum),
    Alias(Annot),
}

impl From<Struct> for UdtKind {
    fn from(s: Struct) -> Self {
        Self::Struct(s)
    }
}

impl From<Enum> for UdtKind {
    fn from(e: Enum) -> Self {
        Self::Enum(e)
    }
}

impl From<Annot> for UdtKind {
    fn from(a: Annot) -> Self {
        Self::Alias(a)
    }
}

#[derive(Debug)]
pub struct Struct {
    pub name: Ident,
    pub fields: Vec<StructField>,
}

#[derive(Debug)]
pub struct StructField {
    pub name: Ident,
    pub ty: Annot,
}

#[derive(Debug)]
pub struct Enum {
    pub name: Ident,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug)]
pub struct EnumVariant {
    pub name: Ident,
    pub data: Option<Spanned<Vec<Annot>>>,
}

#[derive(Debug)]
pub struct Func {
    /// The signature of the function
    pub sig: Sig,
    /// Any generic binders
    pub generics: Option<Generics>,
    /// The id of the function body which, like in rustc, points not to a `Block`, but to an `Expr`.
    pub body: BodyId,
    /// The table in the body of the function: we track this in order to resolve
    /// symbols in its signature (but make sure that it's not redundant to do
    /// so). To resolve symbols in its body, we need the `TableId` held in the
    /// body `Block`.
    pub table: TableId,
    /// `unsafe fn`
    pub is_unsafe: bool,
    /// The name of the function declared at the definition site.
    pub def_name: SymbolId,
    pub span: Span,
}

/// A literal function signature, whose types are not fully resolved
#[derive(Debug)]
pub struct Sig {
    /// Input parameters
    pub params: Vec<Param>,
    /// Return type
    pub output: Option<Annot>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Param {
    /// TODO: This field should really be an `LValue`; that is, a pattern. But for now
    /// we'll accept only identifiers.
    pub name: Ident,
    pub ty: Annot,
    pub span: Span,
}

pub type Generics = Spanned<Vec<GenericBinder>>;

pub type GenericBinder = Spanned<GenericBinderKind>;

#[derive(Debug)]
pub enum GenericBinderKind {
    Lifetime(Lifetime),
    Type(SymbolId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lifetime(pub SymbolId);

impl Into<GenericBinderKind> for Lifetime {
    fn into(self) -> GenericBinderKind {
        GenericBinderKind::Lifetime(self)
    }
}
