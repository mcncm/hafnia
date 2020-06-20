use crate::token::Token;
use std::fmt;

#[derive(Debug)]
pub enum Expression {
    BinOp {
        left: Box<Expression>,
        op: Token,
        right: Box<Expression>,
    },
    UnOp {
        op: Token,
        right: Box<Expression>,
    },
    Literal(Token),
    Variable(Token),
}

impl Expression {}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s_expr = match self {
            Self::BinOp { left, op, right } => format!("({} {} {})", op, left, right),
            Self::UnOp { op, right } => format!("({} {})", op, right),
            Self::Literal(token) => format!("{}", token),
            Self::Variable(token) => format!("{}", token),
        };
        write!(f, "{}", s_expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
