use crate::{context::CtxDisplay, interner_type};
use crate::{
    context::{Context, CtxFmt},
    num::Uint,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

interner_type! { TypeInterner : TyId -> Type }

impl TyId {
    pub fn is_uint(&self, ctx: &Context) -> bool {
        matches!(ctx.types[*self], Type::Uint(_))
    }

    /// Mutually recursive with `Type::is_linear`.
    pub fn is_linear(&self, ctx: &Context) -> bool {
        let ty = &ctx.types[*self];
        ty.is_linear(ctx)
    }
}

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

    /// A function type
    Func(Vec<TyId>, TyId),
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

    pub fn is_linear(&self, ctx: &Context) -> bool {
        match self {
            Type::Bool => false,
            Type::Uint(_) => false,
            Type::Q_Bool => true,
            Type::Q_Uint(_) => true,
            Type::Tuple(tys) => tys.iter().any(|ty| ty.is_linear(ctx)),
            Type::Array(ty) => ty.is_linear(ctx),
            Type::Measured(_) => false,
            // This will become more nuanced when closures are introduced
            Type::Func(_, _) => false,
        }
    }
}

impl CtxDisplay for TyId {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &ctx.types[*self] {
            Type::Bool => f.write_str("bool"),
            Type::Uint(u) => write!(f, "{}", u),
            Type::Q_Bool => f.write_str("?bool"),
            Type::Q_Uint(u) => write!(f, "?{}", u),
            Type::Tuple(tys) => {
                f.write_str("(")?;
                for (n, ty) in tys.iter().enumerate() {
                    if n == tys.len() - 1 {
                        write!(f, "{}", ty.fmt_with(ctx))?;
                    } else {
                        write!(f, "{}, ", ty.fmt_with(ctx))?;
                    }
                }
                f.write_str(")")
            }
            Type::Array(ty) => write!(f, "[{}]", ctx.types[*ty]),
            Type::Measured(ty) => write!(f, "!{}", ctx.types[*ty]),
            Type::Func(tys, ret) => {
                f.write_str("Fn(")?;
                for (n, ty) in tys.iter().enumerate() {
                    if n == tys.len() - 1 {
                        write!(f, "{}", ty.fmt_with(ctx))?;
                    } else {
                        write!(f, "{}, ", ty.fmt_with(ctx))?;
                    }
                }
                write!(f, ") -> {}", ctx.types[*ret])
            }
        }
    }
}

/// Legacy cruft--this is still required by the error formatting.
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("<type>")
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
