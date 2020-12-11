use crate::{ast::Expr, token::Token};
use serde::{Deserialize, Serialize};
use std::fmt;

/// The enum of all the cavy values, comprising the unit type booleans, integers
/// of several sizes, and the quantized counterparts of these types. The
/// quantized integer types are all little-endian by default. In future versions
/// of the compiler, it may be possible to specify the endianness of the backend.
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
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

    // Composite types
    Tuple(Vec<Value>),

    Array(Vec<Value>),

    // Measured value
    Measured(Box<Value>),
}

impl Value {
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Bool(x) => *x,
            _ => todo!(),
        }
    }

    /// Indicates whether a value can be used only once.
    ///
    /// NOTE This function is marked for removal when--and if--we move to static
    /// type-checking.
    #[rustfmt::skip]
    pub fn is_linear(&self) -> bool {
        self.type_of().is_linear()
    }

    pub fn type_of(&self) -> crate::types::Type {
        use crate::types::Type::*;
        use Value::*;
        match self {
            Unit => T_Unit,

            Bool(_) => T_Bool,
            U8(_) => T_U8,
            U16(_) => T_U16,
            U32(_) => T_U32,

            Q_Bool(_) => T_Q_Bool,
            Q_U8(_) => T_Q_U8,
            Q_U16(_) => T_Q_U16,
            Q_U32(_) => T_Q_U32,

            Tuple(data) => T_Tuple(data.iter().map(|elem| elem.type_of()).collect()),

            // NOTE: This here reveals the inadequacy of values, rather than
            // expressions, having types. We can’t know the type of an expression
            // until we evaluate it, but the array might be empty, in which case we
            // cannot evaluate the expression, because it might have side-effects
            // like allocation. We must make some peculiar compromise like arrays
            // being untyped, or empty arrays having their own type.
            Array(data) => T_Array(match data.len() {
                0 => Box::new(T_Unit),
                _ => Box::new(data[0].type_of()),
            }),

            Measured(val) => T_Measured(Box::new(val.type_of())),
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
            _ =>           write!(f, "<{}>", self.type_of()),
        }
    }
}
