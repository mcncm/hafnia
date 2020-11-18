use crate::token::Token;
use std::fmt;

#[derive(Debug, Eq, PartialEq)]
pub enum Expr {
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
    Group(Box<Expr>),
}

impl Expr {}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s_expr = match self {
            Self::BinOp { left, op, right } => format!("({} {} {})", op, left, right),
            Self::UnOp { op, right } => format!("({} {})", op, right),
            Self::Literal(token) => format!("{}", token),
            Self::Variable(token) => format!("{}", token),
            Self::Group(expr) => format!("{}", expr),
        };
        write!(f, "{}", s_expr)
    }
}

#[derive(Debug)]
pub enum Stmt {
    Print(Box<Expr>),
    Expr(Box<Expr>),
    Block(Vec<Box<Stmt>>),
    Assn {
        // lvalues might not just be names! In particular, we would like to make
        // destructuring possible. The same is true of other contexts in which
        // lvalues appear, as in the bound expression in a for loop.
        lhs: Box<Expr>,
        rhs: Vec<Expr>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>,
    },
    For {
        bind: Box<Expr>,
        iter: Box<Expr>,
        body: Box<Stmt>,
    },
}
