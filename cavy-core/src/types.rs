use crate::{
    context::{Context, CtxFmt},
    num::Uint,
};
use crate::{
    context::{CtxDisplay, SymbolId},
    interner_type,
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

    /// Mutually recursive with `Type::size`.
    pub fn size(&self, ctx: &Context) -> TypeSize {
        let ty = &ctx.types[*self];
        ty.size(ctx)
    }

    pub fn slot(&self, elem: usize, ctx: &Context) -> TyId {
        ctx.types[*self].slot(elem)
    }
}

/// This struct tracks the structural properties of a given type
struct StructuralDiscipline {
    linear: bool,
}

/// A struct or enum
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UserType {
    /// The name used at the struct's definition site
    pub def_name: SymbolId,
    /// The fields of the struct / alternatives of the enum, not including its
    /// tag
    pub fields: Vec<(SymbolId, TyId)>,
    /// A (possible) enum tag type
    pub tag: Option<TyId>,
}

impl UserType {
    fn is_enum(&self) -> bool {
        self.tag.is_some()
    }

    fn as_tuple(&self) -> Type {
        Type::Tuple(self.fields.iter().map(|field| field.1).collect())
    }
}

/// The total size of a type, calculated recursively.
pub struct TypeSize {
    /// Number of quantum bits
    pub qsize: usize,
    /// Number of classical bits
    pub csize: usize,
}

impl std::ops::Add for TypeSize {
    type Output = TypeSize;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            qsize: self.qsize + rhs.qsize,
            csize: self.csize + rhs.csize,
        }
    }
}

impl std::iter::Sum<TypeSize> for TypeSize {
    fn sum<I: Iterator<Item = TypeSize>>(iter: I) -> Self {
        let init = TypeSize { qsize: 0, csize: 0 };
        iter.fold(init, |acc, elem| acc + elem)
    }
}

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    /// A function type
    Func(Vec<TyId>, TyId),

    /// A struct or enum
    UserType(UserType),

    /// A provisional experimental type
    Ord,
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

    /// Get the path positions held by this type
    pub fn slot(&self, elem: usize) -> TyId {
        match self {
            Type::Tuple(tys) => tys[elem],
            Type::UserType(_udt) => unimplemented!(),
            _ => unreachable!(),
        }
    }

    /// Number of qubits owned by a type
    pub fn size(&self, ctx: &Context) -> TypeSize {
        match self {
            Type::Bool => TypeSize { qsize: 0, csize: 1 },
            Type::Uint(u) => TypeSize {
                qsize: 0,
                csize: *u as usize,
            },
            Type::Q_Bool => TypeSize { qsize: 1, csize: 0 },
            Type::Q_Uint(u) => TypeSize {
                qsize: *u as usize,
                csize: 0,
            },
            Type::Tuple(elems) => elems.iter().map(|ty| ty.size(ctx)).sum(),
            Type::Array(_) => todo!(),
            Type::Func(_, _) => todo!(),
            Type::UserType(udt) => {
                let tup = udt.as_tuple();
                tup.size(ctx)
            }
            Type::Ord => TypeSize { qsize: 0, csize: 0 },
        }
    }

    pub fn is_linear(&self, ctx: &Context) -> bool {
        match self {
            Type::Bool => false,
            Type::Uint(_) => false,
            Type::Q_Bool => true,
            Type::Q_Uint(_) => true,
            Type::Tuple(tys) => tys.iter().any(|ty| ty.is_linear(ctx)),
            Type::Array(ty) => ty.is_linear(ctx),
            // This will become more nuanced when closures are introduced
            Type::Func(_, _) => false,
            Type::UserType(ty) => {
                let lin_tag = ty.tag.map_or(false, |ty| ty.is_linear(ctx));
                lin_tag || ty.fields.iter().any(|field| field.1.is_linear(ctx))
            }
            Type::Ord => true,
        }
    }

    pub fn is_ord(&self, _ctx: &Context) -> bool {
        match self {
            Type::Ord => true,
            _ => false,
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
            Type::UserType(ty) => write!(f, "{}", ty.def_name.fmt_with(ctx)),
            Type::Ord => write!(f, "ord"),
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
