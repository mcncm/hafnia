use crate::token::Token;
use serde::{Deserialize, Serialize};
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
                    token, token.span, self.msg)
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
    T_Array(Box<Type>),

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

            T_Array(ty) =>      ty.discipline(),

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

            T_Array(ty) => write!(f, "[{}]", ty),

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
        let qubit_array_type = T_Array(Box::new(T_Bool));
        assert!(!qubit_array_type.is_linear());
    }

    /// Arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_2() {
        let qubit_array_type = T_Array(Box::new(T_Q_Bool));
        assert!(qubit_array_type.is_linear());
    }

    /// Arrays of arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_3() {
        let qubit_array_type = T_Array(Box::new(T_Array(Box::new(T_Q_Bool))));
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
