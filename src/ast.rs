use crate::token::Token;
use std::fmt;

#[derive(Debug, Clone)]
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
        lhs: Box<Expr>,
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
}

impl Expr {
    /// Some expressions require semicolons when used in expression statements.
    pub fn requires_semicolon(&self) -> bool {
        use Expr::*;
        match self {
            BinOp { .. } => true,
            UnOp { .. } => true,
            Literal(_) => true,
            Variable(_) => true,
            IntArr { .. } => true,
            ExtArr(_) => true,
            Group(_) => true,
            Block(_, _) => false,
            If { .. } => false,
            Let { .. } => false,
            Call { .. } => true,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Expr::*;
        let s_expr = match self {
            BinOp { left, op, right } => format!("({} {} {})", op, left, right),
            UnOp { op, right } => format!("({} {})", op, right),
            Literal(token) => format!("{}", token),
            Variable(token) => format!("{}", token),
            IntArr { item, reps } => format!("[{}; {}]", item, reps),
            ExtArr(items) => format!("{:#?}", items),
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
            Call {
                callee,
                args,
                paren: _,
            } => {
                format!("({} {:?})", callee, args)
            }
        };
        write!(f, "{}", s_expr)
    }
}

#[derive(Debug, Clone)]
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
    Fn {
        name: Token,
        params: Vec<Token>,
        body: Box<Expr>,
    },
    For {
        bind: Box<Expr>,
        iter: Box<Expr>,
        body: Box<Expr>,
    },
}
