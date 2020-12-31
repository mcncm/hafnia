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
    Bool,
    U8,
    U16,
    U32,

    // Linear types
    Q_Bool,
    Q_U8,
    Q_U16,
    Q_U32,

    // Tuple
    Tuple(Vec<Type>),

    // Array
    Array(Box<Type>),

    // Struct
    Struct(HashMap<String, Type>),

    // Type of measured value
    Measured(Box<Type>),
}

impl Type {
    /// Create an instance of the unit type
    pub fn unit() -> Self {
        Type::Tuple(vec![])
    }

    /// Check the structural properties of each type
    #[rustfmt::skip]
    fn discipline(&self) -> StructuralDiscipline {
        use Type::*;
        match self {
            Bool =>            StructuralDiscipline { linear: false },
            U8 =>              StructuralDiscipline { linear: false },
            U16 =>             StructuralDiscipline { linear: false },
            U32 =>             StructuralDiscipline { linear: false },

            Q_Bool =>          StructuralDiscipline { linear: true },
            Q_U8 =>            StructuralDiscipline { linear: true },
            Q_U16 =>           StructuralDiscipline { linear: true },
            Q_U32 =>           StructuralDiscipline { linear: true },

            Array(ty) =>      ty.discipline(),

            // Tuples and structs are as constrained as their most constrained member
            Tuple(types) =>    StructuralDiscipline {
                linear: types.iter().any(|val| val.discipline().linear),
            },
            Struct(members) => StructuralDiscipline {
                linear: members.values().any(|val| val.discipline().linear),
            },

            Measured(_) =>     StructuralDiscipline { linear: false },
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
            Bool => write!(f, "bool"),
            U8 =>   write!(f, "u8"),
            U16 =>  write!(f, "u16"),
            U32 =>  write!(f, "u32"),

            Q_Bool => write!(f, "?bool"),
            Q_U8 =>   write!(f, "?u8"),
            Q_U16 =>  write!(f, "?u16"),
            Q_U32 =>  write!(f, "?u32"),

            Array(ty) => write!(f, "[{}]", ty),

            Tuple(types) => {
                let repr = types.iter().map(|typ| format!("{}", typ)).collect::<Vec<String>>().join(", ");
                write!(f, "({})", repr)
            }

            Struct { .. } => todo!(),

            Measured(typ) => write!(f, "!{{{}}}", typ),
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
        let qubit_array_type = Array(Box::new(Bool));
        assert!(!qubit_array_type.is_linear());
    }

    /// Arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_2() {
        let qubit_array_type = Array(Box::new(Q_Bool));
        assert!(qubit_array_type.is_linear());
    }

    /// Arrays of arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_3() {
        let qubit_array_type = Array(Box::new(Array(Box::new(Q_Bool))));
        assert!(qubit_array_type.is_linear());
    }

    /// Structs with no linear fields should be nonlinear
    #[test]
    fn structs_inherit_linearity_1() {
        let mut fields = HashMap::new();
        fields.insert(String::from("foo"), U8);
        fields.insert(String::from("bar"), U16);
        assert!(!Struct(fields).is_linear());
    }

    /// Structs with some linear field are linear
    #[test]
    fn structs_inherit_linearity_2() {
        let mut fields = HashMap::new();
        fields.insert(String::from("foo"), U8);
        fields.insert(String::from("bar"), Q_U8);
        assert!(Struct(fields).is_linear());
    }
}
