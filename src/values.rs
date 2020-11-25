use crate::{ast::Expr, token::Token};
use std::fmt;

#[derive(Debug)]
pub struct TypeError {
    msg: &'static str,
    token: Option<Token>,
}

impl fmt::Display for TypeError {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.token {
            Some(token) => {
                write!(f, "Type error at \"{}\" [{}]: {}",
                       token, token.loc, self.msg)
            } ,
            None => {
                write!(f, "Type error: {}", self.msg)
            }
        }
    }
}

impl std::error::Error for TypeError {}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
#[allow(non_camel_case_types)]
pub enum Value {
    Unit,

    // Base types
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),

    // Linearized base types
    Q_Bool(usize),
    Q_U8([usize; 8]),
    Q_U16([usize; 16]),
    Q_U32([usize; 32]),
}

impl Value {
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Bool(x) => *x,
            _ => todo!(),
        }
    }
}

/// Functions: I’ll keep this in this file for now, but note that functions are
/// not first-class in this language, at least for the time being, as this would
/// introduce a bit of extra complexity.
#[derive(Debug, Clone)]
pub struct Func {
    pub params: Vec<String>,
    pub body: Box<Expr>,
}
