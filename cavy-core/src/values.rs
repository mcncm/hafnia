use crate::{ast::Expr, token::Token};
use std::fmt;

/// The enum of all the classical Cavy values, comprising the unit type
/// booleans, integers of several sizes, and the quantized counterparts of these
/// types. The quantized integer types are all little-endian by default. In
/// future versions of the compiler, it may be possible to specify the
/// endianness of the backend.
#[derive(Debug, PartialEq, Eq, Clone)]
#[allow(non_camel_case_types)]
pub enum Value {
    Unit,

    // Base types
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),

    // All composite types are to be represented as lists
    List(Vec<Value>),

    // Provisional, experimental type
    Ord,
}

impl Value {
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Bool(x) => *x,
            _ => todo!(),
        }
    }

    /// Get the path positions held by this value
    pub fn slot(&self, elem: usize) -> &Value {
        match self {
            Value::List(factors) => &factors[elem],
            // Invariant enforced by type checker
            _ => unreachable!(),
        }
    }

    pub fn slot_mut(&mut self, elem: usize) -> &mut Value {
        if let Value::Unit = self {
            let factors = std::iter::repeat(Value::Unit).take(elem).collect();
            *self = Value::List(factors);
        }

        match self {
            Value::List(factors) => {
                if elem >= factors.len() {
                    let diff = 1 + elem - factors.len();
                    factors.extend(std::iter::repeat(Value::Unit).take(diff));
                }
                &mut factors[elem]
            }
            // Invariant enforced by type checker
            _ => {
                unreachable!()
            }
        }
    }

    /// Follow a path to its end from this value
    pub fn follow(&self, path: &[usize]) -> &Value {
        let mut node = self;
        for elem in path {
            node = node.slot(*elem);
        }
        node
    }

    /// Follow a path to its end from this value, mutably
    pub fn follow_mut(&mut self, path: &[usize]) -> &mut Value {
        let mut node = self;
        for elem in path {
            node = node.slot_mut(*elem);
        }
        node
    }
}

impl From<bool> for Value {
    fn from(val: bool) -> Value {
        Value::Bool(val)
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

impl From<()> for Value {
    fn from((): ()) -> Value {
        Value::List(vec![])
    }
}

impl fmt::Display for Value {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Value::*;

        match self {
            Unit =>        write!(f, "()"),

            Bool(x) =>     write!(f, "{}", x),
            U8(x) =>       write!(f, "{}", x),
            U16(x) =>      write!(f, "{}", x),
            U32(x) =>      write!(f, "{}", x),

            List(data) => {
                let repr = data
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "({})", repr)
            }

            Ord => f.write_str("ord"),
        }
    }
}
