use crate::{ast::Expr, token::Token};

/// The enum of all the cavy values, comprising the unit type booleans, integers
/// of several sizes, and the quantized counterparts of these types. The
/// quantized integer types are all little-endian by default. In future versions
/// of the compiler, it may be possible to specify the endianness of the backend.
#[derive(Debug, PartialEq, Eq, Clone)]
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
    Array(types::Type, usize, Vec<Value>),
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

    fn type_of(&self) -> types::Type {
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

            Array(ty, sz, _) => T_Array(Box::new(ty.clone()), *sz),
        }
    }
}

pub mod types {
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
    #[derive(Debug, Clone, PartialEq, Eq)]
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
        T_Array(Box<Type>, usize),

        // Struct
        T_Struct(HashMap<String, Type>),
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

                T_Array(type_, _) => StructuralDiscipline {
                    linear: type_.discipline().linear,
                },

                // Tuples and structs are as constrained as their most constrained member
                T_Tuple(types) =>    StructuralDiscipline {
                    linear: types.iter().any(|val| val.discipline().linear),
                },
                T_Struct(members) => StructuralDiscipline {
                    linear: members.values().any(|val| val.discipline().linear),
                },
            }
        }

        /// Check if the type is linear
        pub fn is_linear(&self) -> bool {
            self.discipline().linear
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use Type::*;

        /// Arrays of nonlinear types should be nonlinear
        #[test]
        fn arrays_inherit_linearity_1() {
            let qubit_array_type = T_Array(Box::new(T_Bool), 4);
            assert!(!qubit_array_type.is_linear());
        }

        /// Arrays of linear types should be linear
        #[test]
        fn arrays_inherit_linearity_2() {
            let qubit_array_type = T_Array(Box::new(T_Q_Bool), 4);
            assert!(qubit_array_type.is_linear());
        }

        /// Arrays of arrays of linear types should be linear
        #[test]
        fn arrays_inherit_linearity_3() {
            let qubit_array_type = T_Array(Box::new(T_Array(Box::new(T_Q_Bool), 3)), 4);
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
