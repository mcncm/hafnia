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
use crate::{index_type, interner_type, store_type};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

// Each of the AST items in this module is given as a wrapper struct (possibly
// with a single field) enclosing an internal enum listing the alternatives for
// that item. This pattern was borrowed from rustc itself, as I found that it
// resolved the problem of a proliferation of AST types for each semantic
// analysis pass.
store_type! { FnStore : FnId -> Func }
store_type! { BodyStore : BodyId -> Expr }
store_type! { TableStore : TableId -> Table }
interner_type! { SymbolStore : SymbolId -> String }

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
    /// Interned strings: identifiers etc.
    pub symbols: SymbolStore,
    /// Symbol tables associated with scoped environments
    pub tables: TableStore,
    /// `main` function
    pub entry_point: Option<FnId>,
}

impl Ast {
    pub fn new() -> Self {
        Self::default()
    }

    /// Try to insert a function into a table.
    /// TODO make this a method of Table
    pub fn insert_fn(&mut self, tab: TableId, symb: SymbolId, func: FnId) -> Option<FnId> {
        self.tables[tab].funcs.insert(symb, func)
    }

    pub fn insert_local(
        &mut self,
        tab: TableId,
        symb: SymbolId,
        ty: Option<Annot>,
    ) -> Option<TableEntry> {
        self.tables[tab].locals.insert(symb, TableEntry::Var(ty))
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

/// A scoped symbol table. This may correspond to a lexical block, module, or
/// function parameters. We should, however, consider splitting those up,
/// possibly using a separate type for function parameters.
#[derive(Debug, Default)]
pub struct Table {
    /// The enclosing scope, if there is any
    pub parent: Option<TableId>,
    /// Locals (`let` bindings) in this scope. Note that these could possibly
    /// point to functions, although there is a separate table of functions
    /// defined in this scope.
    locals: HashMap<SymbolId, TableEntry>,
    /// Functions in this scope. While locals should also be able to "shadow"
    /// functions, and it will one day be possible to define lambda expressions,
    /// this table contains those functions defined with the `fn` keyword. They
    /// must be unique.
    funcs: HashMap<SymbolId, FnId>,
}

impl Table {
    fn new() -> Self {
        Self::default()
    }

    fn child(table: TableId) -> Self {
        Table {
            parent: Some(table),
            locals: HashMap::new(),
            funcs: HashMap::new(),
        }
    }

    /// Look up the data associated with a symbol, recursively
    fn get<'ctx>(&'ctx self, symb: &SymbolId, ctx: &'ctx Ast) -> Option<&'ctx TableEntry> {
        match self.get_inner(symb) {
            v @ Some(_) => v,
            None => match self.parent {
                Some(id) => {
                    let parent = &ctx.tables[id];
                    parent.get(symb, ctx)
                }
                None => None,
            },
        }
    }

    fn get_inner(&self, symb: &SymbolId) -> Option<&TableEntry> {
        // We'll try this: retrieve a local, if one exists, with higher
        // precedence; if there is none, check for a fn item.
        if let Some(entry) = self.locals.get(symb) {
            Some(entry)
        // } else if let Some(fn_id) = self.funcs.get(symb) {
        //     Some(TableEntry::Func(fn_id.clone()))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum TableEntry {
    Var(Option<Annot>),
    Func(FnId),
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
            span: self.span.clone(),
        }
    }
}

/// Interface for ast nodes that can be made from a single token. Returns
/// Err(()) when the received token can't be transformed as the requested node.
pub trait FromToken {
    fn from_token(token: Token, ctx: &mut Ast) -> Result<Self, ()>
    where
        Self: Sized;
}

/// A module. For now there's only one module per program.
pub type Mod = Spanned<Vec<Item>>;

/// Identifier node
pub type Ident = Spanned<SymbolId>;

impl FromToken for Ident {
    fn from_token(token: Token, ctx: &mut Ast) -> Result<Self, ()> {
        use crate::token::Lexeme;
        match token.lexeme {
            Lexeme::Ident(name) => Ok(Self {
                data: ctx.symbols.intern(name),
                span: token.span,
            }),
            _ => Err(()),
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
}

impl FromToken for BinOp {
    fn from_token(token: Token, _ctx: &mut Ast) -> Result<Self, ()> {
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
        };
        write!(f, "{}", repr)
    }
}

/// Unary operator node
pub type UnOp = Spanned<UnOpKind>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOpKind {
    Minus,
    Not,
    Linear,
    Delin,
}

impl FromToken for UnOp {
    fn from_token(token: Token, _ctx: &mut Ast) -> Result<Self, ()> {
        use crate::token::Lexeme::*;
        let kind = match token.lexeme {
            Minus => UnOpKind::Minus,
            Tilde => UnOpKind::Not,
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
    Nat(Unsigned),
}

impl FromToken for Literal {
    fn from_token(token: Token, _ctx: &mut Ast) -> Result<Self, ()> {
        use crate::token::Lexeme::*;
        let kind = match token.lexeme {
            Nat(n) => LiteralKind::Nat(n),
            True => LiteralKind::True,
            False => LiteralKind::False,
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
pub type Expr = Spanned<ExprKind>;

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
    Literal(Literal),
    /// Identifiers
    Ident(Ident),
    /// Sequences of the form (1, 2, 3)
    Tuple(Vec<Expr>),
    /// Intensional arrays of the form [1; 4]
    IntArr {
        item: Box<Expr>,
        reps: Box<Expr>,
    },
    /// Extensional arrays of the form [1, 2, 3]
    ExtArr(Vec<Expr>),
    Block(Box<Block>),
    If {
        cond: Box<Expr>,
        then_branch: Box<Block>,
        else_branch: Option<Box<Block>>,
    },
    For {
        bind: Box<LValue>,
        iter: Box<Expr>,
        body: Box<Block>,
    },
    Call {
        // For the time being, functions are not values, so the callee is not an
        // expression, but just a name. Arguments should also be expressions,
        // but they are currently also just identifiers.
        callee: Ident,
        args: Vec<Expr>,
    },
    Index {
        head: Box<Expr>,
        index: Box<Expr>,
    },
}

impl ExprKind {
    /// Some expressions require semicolons when used in expression statements.
    pub fn requires_semicolon(&self) -> bool {
        use ExprKind::*;
        match self {
            BinOp { .. } => true,
            UnOp { .. } => true,
            Literal(_) => true,
            Ident(_) => true,
            Tuple { .. } => true,
            IntArr { .. } => true,
            ExtArr(_) => true,
            Block(_) => false,
            If { .. } => false,
            For { .. } => false,
            Call { .. } => true,
            Index { .. } => true,
        }
    }
}

/// A brace-delimited code block
#[derive(Debug, Clone)]
pub struct Block {
    /// The statements contained in the block
    pub stmts: Vec<Stmt>,
    /// The terminal expression, if there is one
    pub expr: Option<Box<Expr>>,
    /// The id of the associated symbol table
    pub table: TableId,
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
    Print(Box<Expr>),
    /// An expression without a semicolon.
    Expr(Box<Expr>),
    /// An expression with a semicolon.
    ExprSemi(Box<Expr>),
    /// A variable declaration. The nomenclature here has been taken from
    /// rustc’s ast.rs.
    Local {
        /// lvalues might not just be names! In particular, we would like to make
        /// destructuring possible. The same is true of other contexts in which
        /// lvalues appear, as in the bound expression in a for loop.
        ///
        /// For now, though, we're going to ignore that possibility, disable
        /// destructuring, and allow only a symbol on the lhs.
        lhs: Box<Ident>,
        rhs: Box<Expr>,
    },
    Item(Item),
}

/// An item. For now this wrapper doesn't do anything, but it does make this AST
/// node more symmetric with respect to the others; future refactoring will also
/// be easier, if more fields are added.
pub type Item = Spanned<ItemKind>;

#[derive(Debug, Clone)]
pub enum ItemKind {
    Fn {
        /// Function identifier
        name: Ident,
        /// Function parameters consisting of name-type pairs
        params: Vec<(Ident, Annot)>,
        /// Return type of the function
        typ: Option<Annot>,
        /// Body of the function; guaranteed to be a block.
        body: Box<Block>,
        docstring: Option<String>,
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

/// Type annotations. These are distinct from, and not convertible to types. The
/// reason is that there may be identical type annotations that resolve to
/// different types within different scopes.
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
}

#[derive(Debug)]
pub struct Func {
    /// The signature of the function
    pub sig: Sig,
    /// The id of the function body which, like in rustc, points not to a `Block`, but an `Expr`.
    pub body: BodyId,
    /// The table where the function is defined: we must track this in order to
    /// resolve types in its signature.
    pub table: TableId,
    pub span: Span,
}

/// A function signature
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
