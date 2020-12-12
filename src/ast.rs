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
    Group(Box<Expr>),
    Block(Vec<Stmt>, Option<Box<Expr>>),
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    Let {
        lhs: Box<LValue>,
        rhs: Box<Expr>,
        body: Box<Expr>,
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
            Group(_) => true,
            Block(_, _) => false,
            If { .. } => false,
            Let { .. } => false,
            Call { .. } => true,
            Index { .. } => true,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExprKind::*;
        let s_expr = match &self.kind {
            BinOp { left, op, right } => format!("({} {} {})", op, left, right),
            UnOp { op, right } => format!("({} {})", op, right),
            Literal(token) => format!("{}", token),
            Variable(token) => format!("{}", token),
            Tuple(items) => format!("'({:#?})", items),
            IntArr { item, reps } => format!("[{}; {}]", item, reps),
            ExtArr(items) => format!("[{:#?}]", items),
            Group(expr) => format!("{}", expr),
            If {
                cond,
                then_branch,
                else_branch,
            } => format!("(if {} {} {:#?})", cond, then_branch, else_branch),
            Let { lhs, rhs, body } => format!("(let ({} {}) {})", lhs, rhs, body),
            Block(stmts, expr) => match expr {
                Some(expr) => {
                    format!("(block {:?} {})", stmts, *expr)
                }
                None => {
                    format!("(block {:?})", stmts)
                }
            },
            Call { callee, args, .. } => {
                format!("({} {:?})", callee, args)
            }
            Index { head, index, .. } => {
                format!("(nth {} {})", head, index)
            }
        };
        write!(f, "{}", s_expr)
    }
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
    Expr(Box<Expr>),
    Assn {
        // lvalues might not just be names! In particular, we would like to make
        // destructuring possible. The same is true of other contexts in which
        // lvalues appear, as in the bound expression in a for loop.
        lhs: Box<LValue>,
        /// A type annotation, as in `let x: u8 = 0;`
        ty: Option<Box<Type>>,
        // This should really be an Either<Box<Expr>, Box<Stmt>> where if it’s a
        // Stmt, it’s guaranteed to be a Block
        rhs: Box<Expr>,
    },
    Fn {
        /// Function identifier
        name: Token,
        /// Function parameters consisting of name-type pairs
        params: Vec<(Token, Type)>,
        /// Return type of the function
        typ: Option<Type>,
        /// Body of the function; guaranteed to be a block.
        body: Box<Expr>,
        docstring: Option<String>,
    },
    For {
        bind: Box<LValue>,
        iter: Box<Expr>,
        body: Box<Expr>,
    },
}

/// Something that can be assigned to
#[derive(Debug, Clone)]
pub struct LValue {
    pub kind: LValueKind,
}

impl fmt::Display for LValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LValueKind::*;
        write!(f, "{}", self.kind)
    }
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
    Group(Box<LValue>),
}

impl fmt::Display for LValueKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LValueKind::*;
        match &self {
            Ident(token) => {
                write!(f, "{}", token)
            }
            Tuple(lvalues) => {
                write!(f, "'({:?})", lvalues)
            }
            Group(lvalue) => {
                write!(f, "'({})", lvalue)
            }
        }
    }
}
