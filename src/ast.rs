use crate::token::Token;
use std::fmt;

#[derive(Debug)]
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
    Block(Vec<Stmt>, Option<Box<Expr>>),
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
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
            Self::If {
                cond,
                then_branch,
                else_branch,
            } => format!("(if {} {} {})", cond, then_branch, else_branch),
            Self::Block(stmts, expr) => match expr {
                Some(expr) => {
                    format!("(block {:?} {})", stmts, *expr)
                }
                None => {
                    format!("(block {:?})", stmts)
                }
            },
        };
        write!(f, "{}", s_expr)
    }
}

#[derive(Debug)]
pub enum Stmt {
    Print(Box<Expr>),
    Expr(Box<Expr>),
    Assn {
        // lvalues might not just be names! In particular, we would like to make
        // destructuring possible. The same is true of other contexts in which
        // lvalues appear, as in the bound expression in a for loop.
        lhs: Box<Expr>,
        // This should really be an Either<Box<Expr>, Box<Stmt>> where if it’s a
        // Stmt, it’s guaranteed to be a Block
        rhs: Box<Expr>,
    },
    For {
        bind: Box<Expr>,
        iter: Box<Expr>,
        body: Box<Stmt>,
    },
}
