use crate::{
    context::{Context, CtxFmt},
    num::Uint,
};
use crate::{
    context::{CtxDisplay, SymbolId},
    interner_type,
};
use std::{collections::HashMap, ops::Index};
use std::{fmt, ops::IndexMut};

interner_type! { TypeInterner : TyId -> Type }

/// A type interner that also carries some satellite data caches
pub struct CachedTypeInterner {
    /// The interner proper
    interner: TypeInterner,
    /// A cache of the sizes of each interned type, eliminating the need to
    /// recompute sizes recursively.
    size_cache: HashMap<TyId, TypeSize>,
    /// A cache of the structural properties of each interned type.
    props_cache: HashMap<TyId, StructuralDiscipline>,
}

impl CachedTypeInterner {
    pub fn new() -> Self {
        Self {
            interner: TypeInterner::new(),
            size_cache: HashMap::new(),
            props_cache: HashMap::new(),
        }
    }

    // NOTE This isn't quite perfect: because Types are containers for `TyId`s,
    // not `Box<Type>`s, we'll end up making redundant hashtable lookups when
    // caching a type.
    pub fn intern(&mut self, ty: Type) -> TyId {
        let sz = ty.size(self);
        let props = StructuralDiscipline {
            linear: ty.is_linear(self),
            ord: ty.is_ord(self),
        };
        let ty = self.interner.intern(ty);
        self.size_cache.insert(ty, sz);
        self.props_cache.insert(ty, props);
        ty
    }

    pub fn contains(&self, ty: &Type) -> bool {
        self.interner.contains(ty)
    }

    /// Get the size of an interned typed
    pub fn size_of(&self, ty: &TyId) -> &TypeSize {
        &self.size_cache[ty]
    }

    /// Get the structural properties of an interned type
    pub fn props_of(&self, ty: &TyId) -> &StructuralDiscipline {
        &self.props_cache[ty]
    }
}

impl Index<TyId> for CachedTypeInterner {
    type Output = Type;

    fn index(&self, index: TyId) -> &Self::Output {
        &self.interner[index]
    }
}

impl IndexMut<TyId> for CachedTypeInterner {
    fn index_mut(&mut self, index: TyId) -> &mut Self::Output {
        &mut self.interner[index]
    }
}

impl TyId {
    pub fn is_uint(&self, ctx: &Context) -> bool {
        matches!(ctx.types[*self], Type::Uint(_))
    }

    /// A type will be said to be "classical" if none of the data it points to
    /// is quantum.
    pub fn is_classical(&self, ctx: &Context) -> bool {
        let sz = self.size(ctx);
        sz.qsize == 0
    }

    /// A type will be said to be "coherent" if all of its data is quantum; if
    /// it points to no classical data at all.
    pub fn is_coherent(&self, ctx: &Context) -> bool {
        let sz = self.size(ctx);
        sz.csize == 0
    }

    /// Check the linearity of a type, with the help of the global context
    pub fn is_linear(&self, ctx: &Context) -> bool {
        self.is_linear_inner(&ctx.types)
    }

    fn is_linear_inner(&self, interner: &CachedTypeInterner) -> bool {
        interner.props_of(self).linear
    }

    /// Check the bit size of a type, with the help of the global context
    pub fn size<'a>(&'a self, ctx: &'a Context) -> &'a TypeSize {
        self.size_inner(&ctx.types)
    }

    fn size_inner<'a>(&'a self, interner: &'a CachedTypeInterner) -> &'a TypeSize {
        interner.size_of(self)
    }

    /// Get the stype in the `n`th slot of a type, if it has one.
    pub fn slot(&self, n: usize, ctx: &Context) -> TyId {
        ctx.types[*self].slot(n)
    }
}

/// This struct tracks the structural properties of a given type
pub struct StructuralDiscipline {
    linear: bool,
    ord: bool,
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
#[derive(Clone, Copy)]
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

    /// A linear unsigned integer, like `?7: ?u8`
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
            Type::UserType(udt) => udt.fields[elem].1,
            _ => unreachable!(),
        }
    }

    /// Number of bits owned by a type
    fn size(&self, interner: &CachedTypeInterner) -> TypeSize {
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
            Type::Tuple(elems) => elems
                .iter()
                .map(|ty| ty.size_inner(interner))
                .copied()
                .sum(),
            Type::Array(_) => todo!(),
            Type::Func(_, _) => todo!(),
            Type::UserType(udt) => {
                let tup = udt.as_tuple();
                tup.size(interner)
            }
            Type::Ord => TypeSize { qsize: 0, csize: 0 },
        }
    }

    pub fn is_linear(&self, interner: &CachedTypeInterner) -> bool {
        match self {
            Type::Bool => false,
            Type::Uint(_) => false,
            Type::Q_Bool => true,
            Type::Q_Uint(_) => true,
            Type::Tuple(tys) => tys.iter().any(|ty| ty.is_linear_inner(interner)),
            Type::Array(ty) => ty.is_linear_inner(interner),
            // This will become more nuanced when closures are introduced
            Type::Func(_, _) => false,
            Type::UserType(ty) => {
                let lin_tag = ty.tag.map_or(false, |ty| ty.is_linear_inner(interner));
                lin_tag
                    || ty
                        .fields
                        .iter()
                        .any(|field| field.1.is_linear_inner(interner))
            }
            Type::Ord => true,
        }
    }

    pub fn is_ord(&self, _ctx: &CachedTypeInterner) -> bool {
        matches!(self, Type::Ord)
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
