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

interner_type! { BareTypeInterner : TyId -> Type }

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
    interner: BareTypeInterner,
    /// A cache of the properties of each interned type, eliminating the need to
    /// recompute sizes recursively.
    cache: HashMap<TyId, TypeProperties>,
}

/// A type interner that also carries common types that should be accessible
/// without lookup.
pub struct TypeInterner {
    interner: CachedTypeInterner,
    pub common: CommonTypes,
}

macro_rules! common_types {
    ($($field:ident => $ty:expr),*) => {
        pub struct CommonTypes {
            $(pub $field: TyId),*
        }

        impl TypeInterner {
            pub fn new() -> Self {
                let mut interner = CachedTypeInterner::new();
                $(
                    let $field = interner.intern($ty);
                )*
                let common = CommonTypes {
                    $(
                        $field
                    ),*
                };
                Self {
                    interner,
                    common,
                }
            }
        }
    };

}

common_types! {
    unit => Type::Tuple(vec![]),
    qbool => Type::QBool,
    qu2 => Type::QUint(Uint::U2),
    qu4 => Type::QUint(Uint::U4),
    qu8 => Type::QUint(Uint::U8),
    qu16 => Type::QUint(Uint::U16),
    qu32 => Type::QUint(Uint::U32),
    bool => Type::Ref(RefKind::Shrd, Lifetime::Static, qbool),
    u2 => Type::Ref(RefKind::Shrd, Lifetime::Static, qu2),
    u4 => Type::Ref(RefKind::Shrd, Lifetime::Static, qu4),
    u8 => Type::Ref(RefKind::Shrd, Lifetime::Static, qu8),
    u16 => Type::Ref(RefKind::Shrd, Lifetime::Static, qu16),
    u32 => Type::Ref(RefKind::Shrd, Lifetime::Static, qu32),
    shrd_qbool => Type::Ref(RefKind::Shrd, Lifetime::Static, qbool),
    // This is a provisional type not intended to stay in the compiler forever
    ord => Type::Ord
}

impl CachedTypeInterner {
    fn new() -> Self {
        Self {
            interner: BareTypeInterner::new(),
            cache: HashMap::new(),
        }
    }
    // NOTE This isn't quite perfect: because Types are containers for `TyId`s,
    // not `Box<Type>`s, we'll end up making redundant hashtable lookups when
    // caching a type.
    fn intern(&mut self, ty: Type) -> TyId {
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

impl TypeInterner {
    pub fn intern(&mut self, ty: Type) -> TyId {
        self.interner.intern(ty)
    }
}

impl Index<TyId> for TypeInterner {
    type Output = Type;

    fn index(&self, index: TyId) -> &Self::Output {
        &self.interner.interner[index]
    }
}

impl IndexMut<TyId> for TypeInterner {
    fn index_mut(&mut self, index: TyId) -> &mut Self::Output {
        &mut self.interner.interner[index]
    }
}

impl TyId {
    pub fn is_uint(&self, interner: &TypeInterner) -> bool {
        if let Type::Ref(RefKind::Shrd, Lifetime::Static, _) = interner[*self] {
            matches!(interner[*self], Type::QUint(_))
        } else {
            false
        }
    }

    pub fn is_quint(&self, interner: &TypeInterner) -> bool {
        matches!(interner[*self], Type::QUint(_))
    }

    pub fn is_owned(&self, interner: &TypeInterner) -> bool {
        self.is_owned_inner(&interner.interner)
    }

    fn is_owned_inner(&self, interner: &CachedTypeInterner) -> bool {
        interner.cache[self].owned
    }

    pub fn ref_kind(&self, interner: &TypeInterner) -> Option<RefKind> {
        self.ref_kind_inner(&interner.interner)
    }

    pub fn ref_kind_inner(&self, interner: &CachedTypeInterner) -> Option<RefKind> {
        interner.cache[self].ref_kind
    }

    pub fn referent(&self, ctx: &Context) -> Option<TyId> {
        match &ctx.types[*self] {
            Type::Ref(_, _, ty) => Some(*ty),
            _ => None,
        }
    }

    /// A type will be said to be "classical" if none of the data it contains
    /// is quantum.
    pub fn is_classical(&self, ctx: &Context) -> bool {
        let sz = self.size(ctx);
        sz.qsize == 0
    }

    /// A type will be said to be "coherent" if all of its data is quantum: if
    /// it contains to no classical data at all.
    pub fn is_coherent(&self, ctx: &Context) -> bool {
        let sz = self.size(ctx);
        sz.csize == 0
    }

    pub fn is_primitive(&self, ctx: &Context) -> bool {
        use Type::*;
        match &ctx.types[*self] {
            QBool | QUint(_) => true,
            // The unit type should also be considered primitive
            Tuple(tys) if tys.is_empty() => true,
            _ => false,
        }
    }

    pub fn is_zst(&self, ctx: &Context) -> bool {
        let sz = self.size(ctx);
        sz.csize == 0 && sz.qsize == 0
    }

    /// This type that supports classical bitwise logic operations. A funny name
    /// for this property--should come up with a better one.
    pub fn is_bitlike(&self, ctx: &Context) -> bool {
        let ty = &ctx.types[*self];
        matches!(ty, Type::QBool | Type::QUint(_))
            || if let Type::Ref(RefKind::Shrd, _, inner) = ty {
                let ty = &ctx.types[*inner];
                matches!(ty, Type::QBool | Type::QUint(_))
            } else {
                false
            }
    }

    /// Check the linearity of a type, with the help of the global context
    pub fn is_affine(&self, ctx: &Context) -> bool {
        self.is_affine_inner(&ctx.types.interner)
    }

    fn is_affine_inner(&self, interner: &CachedTypeInterner) -> bool {
        interner.cache[self].affine
    }

    /// Check the bit size of a type, with the help of the global context
    pub fn size<'a>(&'a self, ctx: &'a Context) -> &'a TypeSize {
        self.size_inner(&ctx.types.interner)
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
        let offsets = &ctx.types.interner.cache[self].offsets;
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

    fn mul_scalar(self, rhs: usize) -> Self {
        Self {
            qsize: self.qsize * rhs,
            csize: self.csize * rhs,
        }
    }
}

impl std::ops::Add for TypeSize {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            qsize: self.qsize + rhs.qsize,
            csize: self.csize + rhs.csize,
        }
    }
}

/// A memory location offset for a type slot
#[derive(Debug, Clone, Copy)]
pub struct Offset {
    pub quant: usize,
    pub class: usize,
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

/// Coarse-grained lifetimes: either static or bounded. Unlike in `rustc`, concrete
/// inference variables are not assigned until region inference takes place.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Lifetime {
    /// The static lifetime
    Static,
    /// A non-static lifetime
    Bounded,
}

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// A linear boolean, like `?false`
    QBool,

    /// A linear unsigned integer, like `?7: ?u8`
    QUint(Uint),

    /// Tuples
    Tuple(Vec<TyId>),

    /// Arrays
    Array(TyId, usize),

    /// A function type
    Func(Vec<TyId>, TyId),

    /// A struct or enum
    UserType(UserType),

    /// A reference
    Ref(RefKind, Lifetime, TyId),

    /// A provisional experimental type
    Ord,
}

impl Type {
    /// Create an instance of the unit type
    pub const fn unit() -> Self {
        Self::Tuple(vec![])
    }

    /// Create an instance of the size/index type
    pub const fn size_type(interner: &TypeInterner) -> Self {
        Type::Ref(RefKind::Shrd, Lifetime::Static, interner.common.u32)
    }

    /// Get the path positions held by this type
    pub fn slot(&self, proj: &Proj) -> TyId {
        match (self, proj) {
            (Type::Tuple(tys), Proj::Field(elem)) => tys[*elem],
            (Type::UserType(udt), Proj::Field(elem)) => udt.fields[*elem].1,
            (Type::Ref(_, _, ty), Proj::Deref) => *ty,
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
            Type::QBool => vec![],
            Type::QUint(_) => vec![],
            Type::Tuple(elems) => {
                let offsets: Vec<Offset> = elems
                    .iter()
                    .map(|ty| ty.size_inner(interner))
                    .scan(Offset::zero(), |offset, sz| {
                        let prev_offset = offset.clone();
                        *offset = *offset + *sz;
                        Some(prev_offset)
                    })
                    .collect();
                offsets
            }
            Type::Array(_, _) => vec![],
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
            Type::Ref(_, _, _) => vec![Offset::zero()],
            Type::Ord => vec![],
        }
    }

    /// Compute the number of bits owned by a type.
    fn size(&self, interner: &CachedTypeInterner) -> TypeSize {
        match self {
            Type::QBool => TypeSize { qsize: 1, csize: 0 },
            Type::QUint(u) => TypeSize {
                qsize: *u as usize,
                csize: 0,
            },
            Type::Tuple(elems) => elems
                .iter()
                .map(|ty| ty.size_inner(interner))
                .copied()
                .sum(),
            Type::Array(ty, sz) => ty.size_inner(interner).mul_scalar(*sz),
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
            Type::Ref(_, _, ty) => *ty.size_inner(interner),
            Type::Ord => TypeSize { qsize: 0, csize: 0 },
        }
    }

    pub fn is_owned(&self, interner: &CachedTypeInterner) -> bool {
        match self {
            Type::Tuple(tys) => tys.iter().all(|ty| ty.is_owned_inner(interner)),
            Type::Array(ty, _) => ty.is_owned_inner(interner),
            Type::Func(_, _) => todo!(),
            Type::UserType(ty) => ty.as_tuple().is_owned(interner),
            Type::Ref(_, _, _) => false,
            _ => true,
        }
    }

    pub fn is_affine(&self, interner: &CachedTypeInterner) -> bool {
        match self {
            Type::QBool => true,
            Type::QUint(_) => true,
            Type::Tuple(tys) => tys.iter().any(|ty| ty.is_affine_inner(interner)),
            Type::Array(_, _) => true,
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
            Type::Ref(ref_kind, _, _) => match ref_kind {
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
        if let Type::Ref(ref_kind, _, _) = self {
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
            Type::QBool => f.write_str("qbool"),
            Type::QUint(u) => write!(f, "q{}", u),
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
            Type::Array(ty, sz) => write!(f, "[{}; {}]", ty.fmt_with(ctx), sz),
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
            // TODO This currently doesn't show anything known about the
            // lifetime, whether bounded or static. It could at least
            // distinguish those cases; with further refinement, we could also
            // display e.g. named lifetimes.
            Type::Ref(kind, _, ty) => write!(f, "{}{}", kind, ty.fmt_with(ctx)),
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
        let qubit_array_type = Array(Box::new(QBool));
        assert!(qubit_array_type.is_affine());
    }

    /// Arrays of arrays of linear types should be linear
    #[test]
    fn arrays_inherit_linearity_3() {
        let qubit_array_type = Array(Box::new(Array(Box::new(QBool))));
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
        fields.insert(String::from("bar"), QU8);
        assert!(Struct(fields).is_affine());
    }
}
