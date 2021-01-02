use crate::source::Span;
use crate::token::Token;
use std::convert::TryFrom;
use std::fmt;

// Each of the AST items in this module is given as a wrapper struct (possibly
// with a single field) enclosing an internal enum listing the alternatives for
// that item. This pattern was borrowed from rustc itself, as I found that it
// resolved the problem of a proliferation of AST types for each semantic
// analysis pass.

/// Identifier node
#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// We will sometimes want to convert a token whose lexeme is definitely a
/// `Lexeme::Ident` into this standalone `Ident` node. This implementation will
/// make that easier to do.
impl TryFrom<Token> for Ident {
    /// This is "really" an internal implementation whose use will be pretty
    /// limited; it is supposed to be immediately unwrapped wherever it is used.
    type Error = ();

    fn try_from(token: Token) -> Result<Self, Self::Error> {
        use crate::token::Lexeme;
        match token.lexeme {
            Lexeme::Ident(name) => Ok(Self {
                name,
                span: token.span,
            }),
            _ => Err(()),
        }
    }
}

/// Binary operator node
#[derive(Debug, Clone)]
pub struct BinOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

/// We will sometimes want to convert a token whose lexeme is definitely a
/// binary operator into this standalone `BinOp` node. This implementation will
/// make that easier to do.
impl TryFrom<Token> for BinOp {
    /// This is "really" an internal implementation whose use will be pretty
    /// limited; it is supposed to be immediately unwrapped wherever it is used.
    type Error = ();

    fn try_from(token: Token) -> Result<Self, Self::Error> {
        use crate::token::Lexeme::*;
        let kind = match token.lexeme {
            EqualEqual => BinOpKind::Equal,
            TildeEqual => BinOpKind::Nequal,
            DotDot => BinOpKind::DotDot,
            Plus => BinOpKind::Plus,
            Minus => BinOpKind::Minus,
            Star => BinOpKind::Times,
            Percent => BinOpKind::Mod,
            LAngle => BinOpKind::Less,
            RAngle => BinOpKind::Greater,
            _ => {
                return Err(());
            }
        };
        Ok(BinOp {
            kind,
            span: token.span,
        })
    }
}

/// Unary operator node
#[derive(Debug, Clone)]
pub struct UnOp {
    pub kind: UnOpKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOpKind {
    Minus,
    Not,
    Linear,
    Delin,
}

/// We will sometimes want to convert a token whose lexeme is definitely a
/// unary operator into this standalone `UnOp` node. This implementation will
/// make that easier to do.
impl TryFrom<Token> for UnOp {
    /// This is "really" an internal implementation whose use will be pretty
    /// limited; it is supposed to be immediately unwrapped wherever it is used.
    type Error = ();

    fn try_from(token: Token) -> Result<Self, Self::Error> {
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
            kind,
            span: token.span,
        })
    }
}
/// Expression node.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub tags: ExprTags,
    pub span: Span,
}

impl From<ExprKind> for Expr {
    fn from(kind: ExprKind) -> Self {
        Self {
            kind,
            tags: ExprTags::default(),
            span: Span::default(),
        }
    }
}

/// Decorations added to an expression node through successive compiler passes.
#[derive(Default, Debug, Clone)]
pub struct ExprTags {}

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
    Literal(Token),
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
    Block(Block),
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
    Let {
        lhs: Box<LValue>,
        rhs: Box<Expr>,
        body: Box<Block>,
    },
    Call {
        // For the time being, functions are not values, so the callee is not an
        // expression, but just a name. Arguments should also be expressions,
        // but they are currently also just identifiers.
        callee: Ident,
        args: Vec<Expr>,
        paren: Token,
    },
    Index {
        head: Box<Expr>,
        index: Box<Expr>,
        bracket: Token,
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
            Let { .. } => false,
            Call { .. } => true,
            Index { .. } => true,
        }
    }
}

// A brace-delimited code block
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

/// Statement node.
#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

impl From<StmtKind> for Stmt {
    fn from(kind: StmtKind) -> Self {
        Self {
            kind,
            span: Span::default(),
        }
    }
}

/// A kind of statement
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
        lhs: Box<LValue>,
        /// A type annotation, as in `let x: u8 = 0;`
        ty: Option<Annot>,
        rhs: Box<Expr>,
    },
    Item(Item),
}

impl StmtKind {
    /// Checks whether the statement is an item. This is used for hoisting in
    /// semantic analysis phases.
    pub fn is_item(&self) -> bool {
        matches!(self, StmtKind::Item(_))
    }
}

/// An item. For now this wrapper doesn't do anything, but it does make this AST
/// node more symmetric with respect to the others; future refactoring will also
/// be easier, if more fields are added.
#[derive(Debug, Clone)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Fn {
        /// Function identifier
        name: String,
        /// Function parameters consisting of name-type pairs
        params: Vec<(String, Annot)>,
        /// Return type of the function
        typ: Option<Annot>,
        /// Body of the function; guaranteed to be a block.
        body: Box<Block>,
        docstring: Option<String>,
    },
}

/// Something that can be assigned to
#[derive(Debug, Clone)]
pub struct LValue {
    pub kind: LValueKind,
    pub span: Span,
}

impl From<LValueKind> for LValue {
    fn from(kind: LValueKind) -> Self {
        Self {
            kind,
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
#[derive(Debug, Clone)]
pub struct Annot {
    pub kind: AnnotKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum AnnotKind {
    Bool,
    U8,
    U16,
    U32,

    Tuple(Vec<Annot>),
    Array(Box<Annot>),

    /// Linearization of a type annotation: e.g. `?u8`
    Question(Box<Annot>),
    /// Delinearization of a type annotation: e.g. `!Cat`
    Bang(Box<Annot>),

    /// User-defined types
    Ident(Ident),
}
