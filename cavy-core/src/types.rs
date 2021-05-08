use crate::{
    context::{Context, SymbolId},
    interner_type,
    mir::Proj,
    num::Uint,
    util::{FmtWith, FmtWrapper},
};
use std::{
    collections::HashMap,
    fmt,
    ops::{Index, IndexMut},
};

interner_type! { TypeInterner : TyId -> Type }

/// A type properties table to be computed once and stored in the
/// `CachedTypeInterner`.
pub struct TypeProperties {
    /// The number of quantum and classical bits referenced by this type
    size: TypeSize,
    /// True if this type is uncloneable
    affine: bool,
    /// True if this type is owned
    owned: bool,
    /// True if the type is ord
    ord: bool,
    /// If a reference, the kind of reference that it is
    ref_kind: Option<RefKind>,
    /// Precomputed memory offsets for the type slots
    offsets: Vec<Offset>,
}

/// A type interner that also carries some satellite data caches
pub struct CachedTypeInterner {
    /// The interner proper
    interner: TypeInterner,
    /// A cache of the properties of each interned type, eliminating the need to
    /// recompute sizes recursively.
    cache: HashMap<TyId, TypeProperties>,
}

impl CachedTypeInterner {
    pub fn new() -> Self {
        Self {
            interner: TypeInterner::new(),
            cache: HashMap::new(),
        }
    }

    // NOTE This isn't quite perfect: because Types are containers for `TyId`s,
    // not `Box<Type>`s, we'll end up making redundant hashtable lookups when
    // caching a type.
    pub fn intern(&mut self, ty: Type) -> TyId {
        let props = TypeProperties {
            size: ty.size(self),
            owned: ty.is_owned(self),
            affine: ty.is_affine(self),
            ord: ty.is_ord(self),
            ref_kind: ty.ref_kind(self),
            offsets: ty.offsets(self),
        };
        let ty = self.interner.intern(ty);
        self.cache.insert(ty, props);
        ty
    }

    pub fn contains(&self, ty: &Type) -> bool {
        self.interner.contains(ty)
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

    pub fn is_owned(&self, ctx: &Context) -> bool {
        self.is_owned_inner(&ctx.types)
    }

    fn is_owned_inner(&self, interner: &CachedTypeInterner) -> bool {
        interner.cache[self].owned
    }

    pub fn ref_kind(&self, ctx: &Context) -> Option<RefKind> {
        self.ref_kind_inner(&ctx.types)
    }

    pub fn ref_kind_inner(&self, interner: &CachedTypeInterner) -> Option<RefKind> {
        interner.cache[self].ref_kind
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

    pub fn is_primitive(&self, ctx: &Context) -> bool {
        match &ctx.types[*self] {
            Type::Tuple(_) => false,
            Type::Array(_) => false,
            Type::Func(_, _) => false,
            Type::UserType(_) => false,
            _ => true,
        }
    }

    /// Check the linearity of a type, with the help of the global context
    pub fn is_affine(&self, ctx: &Context) -> bool {
        self.is_affine_inner(&ctx.types)
    }

    fn is_affine_inner(&self, interner: &CachedTypeInterner) -> bool {
        interner.cache[self].affine
    }

    /// Check the bit size of a type, with the help of the global context
    pub fn size<'a>(&'a self, ctx: &'a Context) -> &'a TypeSize {
        self.size_inner(&ctx.types)
    }

    fn size_inner<'a>(&'a self, interner: &'a CachedTypeInterner) -> &'a TypeSize {
        &interner.cache[self].size
    }

    // I'm not sure about this interface. I don't realy want to store the slot
    // types *twice*, but it also seems a little weird to take the offset from a
    // different place than the inner type, and it's also a little weird for
    // this to have a different "signature" than `Type::slot`.
    /// Get the type in a projection, if this type has one.
    pub fn slot(&self, proj: &Proj, ctx: &Context) -> (TyId, Offset) {
        let ty = &ctx.types[*self];
        let inner = ty.slot(proj);
        let offsets = &ctx.types.cache[self].offsets;
        let offset = match proj {
            Proj::Field(n) => offsets[*n],
            Proj::Deref => offsets[0],
        };
        (inner, offset)
    }

    /// Resolve a path of projections
    pub fn project(&self, projections: &[Proj], ctx: &Context) -> TyId {
        projections.iter().fold(*self, |ty, proj| {
            let ty = &ctx.types[ty];
            ty.slot(proj)
        })
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
    /// The fields of the struct / variants of the enum, not including its
    /// tag
    pub fields: Vec<(SymbolId, TyId)>,
    /// A (possible) enum tag type
    pub tag: Option<Discriminant>,
}

impl UserType {
    fn is_enum(&self) -> bool {
        self.tag.is_some()
    }

    fn is_struct(&self) -> bool {
        self.tag.is_none()
    }

    fn as_tuple(&self) -> Type {
        Type::Tuple(self.fields.iter().map(|field| field.1).collect())
    }
}

/// An enum discriminant is a small number of either cbits or qbits
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Discriminant {
    C(usize),
    Q(usize),
}

impl Discriminant {
    fn is_affine(&self) -> bool {
        if let Self::Q(_) = self {
            true
        } else {
            false
        }
    }
}

/// The total size of a type, calculated recursively.
#[derive(Debug, Clone, Copy)]
pub struct TypeSize {
    /// Number of quantum bits
    pub qsize: usize,
    /// Number of classical bits
    pub csize: usize,
}

impl TypeSize {
    pub fn zero() -> Self {
        Self { qsize: 0, csize: 0 }
    }

    /// Construct a type size of a classical type of size `n`
    pub fn classical(n: usize) -> Self {
        Self { qsize: n, csize: 0 }
    }

    /// Construct a type size of a "coherent" (all-quantum) type of size `n.`
    pub fn coherent(n: usize) -> Self {
        Self { qsize: 0, csize: n }
    }

    /// Take the componentwise maximum of two type sizes
    pub fn join_max(&self, other: &TypeSize) -> Self {
        Self {
            qsize: std::cmp::max(self.qsize, other.qsize),
            csize: std::cmp::max(self.csize, other.qsize),
        }
    }
}

/// A memory location offset for a type slot
#[derive(Debug, Clone, Copy)]
pub struct Offset {
    pub quant: usize,
    pub class: usize,
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

impl std::ops::Add<TypeSize> for Offset {
    type Output = Offset;

    fn add(self, rhs: TypeSize) -> Self::Output {
        Self {
            quant: self.quant + rhs.qsize,
            class: self.class + rhs.csize,
        }
    }
}

impl std::ops::Add<Offset> for Offset {
    type Output = Offset;

    fn add(self, rhs: Offset) -> Self::Output {
        Self {
            quant: self.quant + rhs.quant,
            class: self.class + rhs.class,
        }
    }
}

impl From<TypeSize> for Offset {
    fn from(sz: TypeSize) -> Self {
        Self {
            quant: sz.qsize,
            class: sz.csize,
        }
    }
}

impl Offset {
    pub fn zero() -> Self {
        Self { quant: 0, class: 0 }
    }
}

impl std::iter::Sum<TypeSize> for TypeSize {
    fn sum<I: Iterator<Item = TypeSize>>(iter: I) -> Self {
        let init = TypeSize { qsize: 0, csize: 0 };
        iter.fold(init, |acc, elem| acc + elem)
    }
}

/// Kinds of reference types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefKind {
    /// A shared reference
    Shrd,
    /// A unique reference
    Uniq,
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

    /// A reference
    Ref(RefKind, TyId),

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
    pub fn slot(&self, proj: &Proj) -> TyId {
        match (self, proj) {
            (Type::Tuple(tys), Proj::Field(elem)) => tys[*elem],
            (Type::UserType(udt), Proj::Field(elem)) => udt.fields[*elem].1,
            (Type::Ref(_, ty), Proj::Deref) => *ty,
            _ => unreachable!(),
        }
    }

    // TODO: this method can/should probably be unified with `Type::slot` and/or
    // `Type::size`; it's really *doubling* the work of interning.
    //
    // On second thought, maybe don't. They're deceptively combinable-looking,
    // but each one has enough special cases that it comes out a little ugly.
    /// Compute the memory offsets of the type's slots
    fn offsets(&self, interner: &CachedTypeInterner) -> Vec<Offset> {
        match self {
            Type::Bool => vec![],
            Type::Uint(_) => vec![],
            Type::Q_Bool => vec![],
            Type::Q_Uint(_) => vec![],
            Type::Tuple(elems) => {
                let mut offsets: Vec<Offset> = elems
                    .iter()
                    .map(|ty| ty.size_inner(interner))
                    .scan(Offset::zero(), |offset, sz| {
                        let prev_offset = offset.clone();
                        *offset = *offset + *sz;
                        Some(prev_offset)
                    })
                    .collect();
                // The last offset is the size of the tuple, which is what makes
                // it so appealing to try combining this wtih `Type::size`.
                offsets.pop();
                offsets
            }
            Type::Array(_) => todo!(),
            Type::Func(_, _) => vec![],
            Type::UserType(udt) => {
                if let Some(tag) = &udt.tag {
                    let tag_size = match tag {
                        Discriminant::C(n) => TypeSize::classical(*n),
                        Discriminant::Q(n) => TypeSize::coherent(*n),
                    };
                    return vec![Offset::from(tag_size)];
                } else {
                    let tuple = udt.as_tuple();
                    return tuple.offsets(interner);
                }
            }
            // There should be one offset *to the owned data*, which is just
            // contained in the ref. This is in contrast with Rust, where a
            // reference is of constant size.
            Type::Ref(_, _) => vec![Offset::zero()],
            Type::Ord => vec![],
        }
    }

    /// Compute the number of bits owned by a type.
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
            Type::UserType(udt) => match &udt.tag {
                // The enum case is special, and we'll treat it separately with an early return
                Some(tag) => {
                    let tag_size = match tag {
                        Discriminant::C(n) => TypeSize::classical(*n),
                        Discriminant::Q(n) => TypeSize::coherent(*n),
                    };
                    udt.fields
                        .iter()
                        .map(|(_, ty)| ty.size_inner(interner))
                        .fold(tag_size, |acc, sz| acc.join_max(sz))
                }
                None => {
                    let tup = udt.as_tuple();
                    tup.size(interner)
                }
            },
            // Note that this is different from Rust: a 'reference' isn't a
            // fixed-size reference at all; it's actually the original data in
            // memory. It's just the usage contract that differs.
            Type::Ref(_, ty) => *ty.size_inner(interner),
            Type::Ord => TypeSize { qsize: 0, csize: 0 },
        }
    }

    pub fn is_owned(&self, interner: &CachedTypeInterner) -> bool {
        match self {
            Type::Tuple(tys) => tys.iter().all(|ty| ty.is_owned_inner(interner)),
            Type::Array(_ty) => todo!(),
            Type::Func(_, _) => todo!(),
            Type::UserType(ty) => ty.as_tuple().is_owned(interner),
            Type::Ref(_, _) => false,
            _ => true,
        }
    }

    pub fn is_affine(&self, interner: &CachedTypeInterner) -> bool {
        match self {
            Type::Bool => false,
            Type::Uint(_) => false,
            Type::Q_Bool => true,
            Type::Q_Uint(_) => true,
            Type::Tuple(tys) => tys.iter().any(|ty| ty.is_affine_inner(interner)),
            Type::Array(ty) => ty.is_affine_inner(interner),
            // This will become more nuanced when closures are introduced
            Type::Func(_, _) => false,
            Type::UserType(ty) => {
                let lin_tag = ty.tag.as_ref().map_or(false, |ty| ty.is_affine());
                lin_tag
                    || ty
                        .fields
                        .iter()
                        .any(|field| field.1.is_affine_inner(interner))
            }
            Type::Ref(ref_kind, _) => match ref_kind {
                RefKind::Shrd => false,
                RefKind::Uniq => true,
            },
            Type::Ord => true,
        }
    }

    pub fn is_ord(&self, _ctx: &CachedTypeInterner) -> bool {
        matches!(self, Type::Ord)
    }

    pub fn ref_kind(&self, _interner: &CachedTypeInterner) -> Option<RefKind> {
        if let Type::Ref(ref_kind, _) = self {
            Some(*ref_kind)
        } else {
            None
        }
    }
}

impl fmt::Display for RefKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefKind::Shrd => f.write_str("&"),
            RefKind::Uniq => f.write_str("&mut "),
        }
    }
}

impl<'c> FmtWith<Context<'c>> for TyId {
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
            Type::Ref(kind, ty) => write!(f, "{}{}", kind, ty.fmt_with(ctx)),
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
        assert!(!qubit_array_type.is_affine());
    }

    /// Arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_2() {
        let qubit_array_type = Array(Box::new(Q_Bool));
        assert!(qubit_array_type.is_affine());
    }

    /// Arrays of arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_3() {
        let qubit_array_type = Array(Box::new(Array(Box::new(Q_Bool))));
        assert!(qubit_array_type.is_affine());
    }

    /// Structs with no linear fields should be nonlinear
    #[test]
    fn structs_inherit_linearity_1() {
        let mut fields = HashMap::new();
        fields.insert(String::from("foo"), U8);
        fields.insert(String::from("bar"), U16);
        assert!(!Struct(fields).is_affine());
    }

    /// Structs with some linear field are linear
    #[test]
    fn structs_inherit_linearity_2() {
        let mut fields = HashMap::new();
        fields.insert(String::from("foo"), U8);
        fields.insert(String::from("bar"), Q_U8);
        assert!(Struct(fields).is_affine());
    }
}
