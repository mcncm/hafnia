use crate::interner_type;
use crate::num::Uint;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

interner_type! { TyInterner: TyId -> Type }

/// This struct tracks the structural properties of a given type
struct StructuralDiscipline {
    linear: bool,
}

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// A non-linear (classical) boolean
    Bool,

    /// A non-linear (classical) unsigned integer
    Uint(Uint),

    /// A linear boolean, like `?false`
    Q_Bool,

    /// A linear unsigned integer, like `?7`
    Q_Uint(Uint),

    /// Tuples
    Tuple(Vec<TyId>),

    /// Arrays
    Array(TyId),

    /// Wrapper type of measured value
    Measured(TyId),
}

impl Type {
    /// Create an instance of the unit type
    pub const fn unit() -> Self {
        Self::Tuple(vec![])
    }

    /// Create an instance of the size/index type
    pub const fn size_type() -> Self {
        Type::Uint(Uint::U32)
    }
}

impl fmt::Display for Type {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<type>")
    }
}

#[cfg(foo)]
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
