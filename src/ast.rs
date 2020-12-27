use crate::token::Token;
use crate::types::Type;
use std::fmt;

// Each of the AST items in this module is given as a wrapper struct (possibly
// with a single field) enclosing an internal enum listing the alternatives for
// that item. This pattern was borrowed from rustc itself, as I found that it
// resolved the problem of a proliferation of AST types for each semantic
// analysis pass.

/// Expression node.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub tags: ExprTags,
}

impl From<ExprKind> for Expr {
    fn from(kind: ExprKind) -> Self {
        Self {
            kind,
            tags: ExprTags::default(),
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
        op: Token,
        right: Box<Expr>,
    },
    UnOp {
        op: Token,
        right: Box<Expr>,
    },
    Literal(Token),
    Variable(Token),
    // Sequences of the form (1, 2, 3)
    Tuple(Vec<Expr>),
    // Intensional arrays of the form [1; 4]
    IntArr {
        item: Box<Expr>,
        reps: Box<Expr>,
    },
    // Extensional arrays of the form [1, 2, 3]
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
        callee: Box<Token>,
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
            Variable(_) => true,
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
}

impl From<StmtKind> for Stmt {
    fn from(kind: StmtKind) -> Self {
        Self { kind }
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
        ty: Option<Box<Type>>,
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
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Fn {
        /// Function identifier
        name: Token,
        /// Function parameters consisting of name-type pairs
        params: Vec<(Token, Type)>,
        /// Return type of the function
        typ: Option<Type>,
        /// Body of the function; guaranteed to be a block.
        body: Box<Block>,
        docstring: Option<String>,
    },
}

/// Something that can be assigned to
#[derive(Debug, Clone)]
pub struct LValue {
    pub kind: LValueKind,
}

impl From<LValueKind> for LValue {
    fn from(kind: LValueKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone)]
pub enum LValueKind {
    Ident(Token),
    /// Sequence of the form (a, b, c)
    Tuple(Vec<LValue>),
}
