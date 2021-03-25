use crate::{ast::Expr, token::Token};
use serde::{Deserialize, Serialize};
use std::fmt;

/// The enum of all the classical Cavy values, comprising the unit type
/// booleans, integers of several sizes, and the quantized counterparts of these
/// types. The quantized integer types are all little-endian by default. In
/// future versions of the compiler, it may be possible to specify the
/// endianness of the backend.
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
#[allow(non_camel_case_types)]
pub enum Value {
    Unit,

    // Base types
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),

    // Composite types
    Tuple(Vec<Value>),

    Array(Vec<Value>),
}

impl Value {
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Bool(x) => *x,
            _ => todo!(),
        }
    }

    pub fn make_range<T>(lower: T, upper: T) -> Self
    where
        std::ops::Range<T>: IntoIterator,
        // This is pretty verbose. Why doesn’t a simple `T: Into<Self>` or
        // `Self: From<T>` bound work?
        Self: From<<std::ops::Range<T> as IntoIterator>::Item>,
    {
        let values = (lower..upper).into_iter().map(|val| val.into()).collect();
        Value::Array(values)
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
        Value::Tuple(vec![])
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

            Array(data) => {
                let repr = data
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "[{}]", repr)
            }

            Tuple(data) => {
                let repr = data
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "({})", repr)
            }
            _ =>           write!(f, "<value>"),
        }
    }
}
