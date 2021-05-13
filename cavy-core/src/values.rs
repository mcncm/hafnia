//! The representaiton of classical values used by the current constant
//! propagation code, which is due for replacement.

// In fact, I could use the generic place tree that was added recently.

use crate::{ast::Expr, mir::Proj, num::USmall, token::Token};
use std::fmt;

/// The enum of primitive classical Cavy values expressible by literals
#[derive(Debug, PartialEq, Eq, Clone)]
#[allow(non_camel_case_types)]
pub enum Value {
    // NOTE Here the unit value isn't equal to the empty tuple value, although
    // the types are equal. Is that a problem?
    Unit,

    // Base types
    Bool(bool),
    U2(USmall<2>),
    U4(USmall<4>),
    U8(u8),
    U16(u16),
    U32(u32),
    Ord,
}

impl Value {
    pub fn size(&self) -> usize {
        use Value::*;
        match self {
            Unit => 0,
            Bool(_) => 1,
            U2(_) => 2,
            U4(_) => 4,
            U8(_) => 8,
            U16(_) => 16,
            U32(_) => 32,
            Ord => 0,
        }
    }

    // TODO: [PERF] the allocation here is very unsatisfying; unfortunately,
    // it's not straightforward to do this entirely with allocation-free lazy
    // iterators.
    //
    // Could *at least* use a bitvec or something
    pub fn bits(&self) -> Vec<bool> {
        match self {
            Value::Unit => vec![],
            Value::Bool(b) => vec![*b],
            // don't bother trying to make these nice and generic (yet); it
            // turns out to be a slight pain
            Value::U2(n) => (0..2).map(|i| (u8::from(*n) & (1 << i)) != 0).collect(),
            Value::U4(n) => (0..4).map(|i| (u8::from(*n) & (1 << i)) != 0).collect(),
            Value::U8(n) => (0..8).map(|i| (n & (1 << i)) != 0).collect(),
            Value::U16(n) => (0..16).map(|i| (n & (1 << i)) != 0).collect(),
            Value::U32(n) => (0..32).map(|i| (n & (1 << i)) != 0).collect(),
            Value::Ord => unimplemented!(),
        }
    }
}

impl From<bool> for Value {
    fn from(val: bool) -> Value {
        Value::Bool(val)
    }
}

impl From<USmall<2>> for Value {
    fn from(val: USmall<2>) -> Value {
        Value::U2(val)
    }
}

impl From<USmall<4>> for Value {
    fn from(val: USmall<4>) -> Value {
        Value::U4(val)
    }
}

impl From<u8> for Value {
    fn from(val: u8) -> Value {
        Value::U8(val)
    }
}

impl From<u16> for Value {
    fn from(val: u16) -> Value {
        Value::U16(val)
    }
}

impl From<u32> for Value {
    fn from(val: u32) -> Value {
        Value::U32(val)
    }
}

impl fmt::Display for Value {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Value::*;

        match self {
            Unit =>        write!(f, "()"),

            Bool(x) =>     write!(f, "{}", x),
            U2(x) =>       write!(f, "{}", x),
            U4(x) =>       write!(f, "{}", x),
            U8(x) =>       write!(f, "{}", x),
            U16(x) =>      write!(f, "{}", x),
            U32(x) =>      write!(f, "{}", x),
            Ord =>         f.write_str("ord"),
        }
    }
}
