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

    pub fn type_of(&self) -> types::Type {
        use types::Type::*;
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
            //
            // The peculiar compromise I’ll choose is that arrays *maybe*
            // contain their type; if empty, there is no type for them to
            // contain.
            Array(data) => T_Array(
                match data.len() {
                    0 => Box::new(None),
                    _ => Box::new(Some(data[0].type_of())),
                },
                data.len(),
            ),

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

pub mod types {
    use super::{Deserialize, Serialize};
    use crate::token::Token;
    use std::collections::HashMap;
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

    /// This struct tracks the structural properties of a given type
    struct StructuralDiscipline {
        linear: bool,
    }

    #[allow(non_camel_case_types)]
    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
    pub enum Type {
        T_Unit,

        T_Bool,
        T_U8,
        T_U16,
        T_U32,

        // Linear types
        T_Q_Bool,
        T_Q_U8,
        T_Q_U16,
        T_Q_U32,

        // Tuple
        T_Tuple(Vec<Type>),

        // Array
        T_Array(Box<Option<Type>>, usize),

        // Struct
        T_Struct(HashMap<String, Type>),

        // Type of measured value
        T_Measured(Box<Type>),
    }

    impl Type {
        /// Check the structural properties of each type
        #[rustfmt::skip]
        fn discipline(&self) -> StructuralDiscipline {
            use Type::*;
            match self {
                T_Unit =>            StructuralDiscipline { linear: false },
                T_Bool =>            StructuralDiscipline { linear: false },
                T_U8 =>              StructuralDiscipline { linear: false },
                T_U16 =>             StructuralDiscipline { linear: false },
                T_U32 =>             StructuralDiscipline { linear: false },

                T_Q_Bool =>          StructuralDiscipline { linear: true },
                T_Q_U8 =>            StructuralDiscipline { linear: true },
                T_Q_U16 =>           StructuralDiscipline { linear: true },
                T_Q_U32 =>           StructuralDiscipline { linear: true },

                T_Array(typ, _) =>   StructuralDiscipline {
                    linear: match &**typ {
                        Some(typ) => typ.discipline().linear,
                        None => false,
                    }
                },

                // Tuples and structs are as constrained as their most constrained member
                T_Tuple(types) =>    StructuralDiscipline {
                    linear: types.iter().any(|val| val.discipline().linear),
                },
                T_Struct(members) => StructuralDiscipline {
                    linear: members.values().any(|val| val.discipline().linear),
                },

                T_Measured(_) =>     StructuralDiscipline { linear: false },
            }
        }

        /// Check if the type is linear
        pub fn is_linear(&self) -> bool {
            self.discipline().linear
        }
    }

    impl fmt::Display for Type {
        #[rustfmt::skip]
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            use Type::*;

            match self {
                T_Unit => write!(f, "()"),

                T_Bool => write!(f, "bool"),
                T_U8 =>   write!(f, "u8"),
                T_U16 =>  write!(f, "u16"),
                T_U32 =>  write!(f, "u32"),

                T_Q_Bool => write!(f, "?bool"),
                T_Q_U8 =>   write!(f, "?u8"),
                T_Q_U16 =>  write!(f, "?u16"),
                T_Q_U32 =>  write!(f, "?u32"),

                // As above, this case reveals the inadequacy of dynamic typing
                T_Array(typ, len) => {
                    let typ = typ.as_ref().as_ref().unwrap();
                    match len {
                        0 => write!(f, "[_; 0]"),
                        l => write!(f, "[{}; {}]", typ, l),
                    }
                }

                T_Tuple(types) => {
                    let repr = types.iter().map(|typ| format!("{}", typ)).collect::<Vec<String>>().join(", ");
                    write!(f, "({})", repr)
                }

                T_Struct { .. } => todo!(),

                T_Measured(typ) => write!(f, "!{{{}}}", typ),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use Type::*;

        /// Arrays of nonlinear types should be nonlinear
        #[test]
        fn arrays_inherit_linearity_1() {
            let qubit_array_type = T_Array(Box::new(Some(T_Bool)), 4);
            assert!(!qubit_array_type.is_linear());
        }

        /// Arrays of linear types should be linear
        #[test]
        fn arrays_inherit_linearity_2() {
            let qubit_array_type = T_Array(Box::new(Some(T_Q_Bool)), 4);
            assert!(qubit_array_type.is_linear());
        }

        /// Arrays of arrays of linear types should be linear
        #[test]
        fn arrays_inherit_linearity_3() {
            let qubit_array_type = T_Array(Box::new(Some(T_Array(Box::new(Some(T_Q_Bool)), 3))), 4);
            assert!(qubit_array_type.is_linear());
        }

        /// Structs with no linear fields should be nonlinear
        #[test]
        fn structs_inherit_linearity_1() {
            let mut fields = HashMap::new();
            fields.insert(String::from("foo"), T_U8);
            fields.insert(String::from("bar"), T_U16);
            assert!(!T_Struct(fields).is_linear());
        }

        /// Structs with some linear field are linear
        #[test]
        fn structs_inherit_linearity_2() {
            let mut fields = HashMap::new();
            fields.insert(String::from("foo"), T_U8);
            fields.insert(String::from("bar"), T_Q_U8);
            assert!(T_Struct(fields).is_linear());
        }
    }
}
