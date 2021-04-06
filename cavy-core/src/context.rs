//! This module is home to the `Context` data structure central to the
//! compilation process.

use crate::session::{Config, Phase};
use crate::source::{SrcId, SrcStore};
use crate::types::{CachedTypeInterner, TyId, Type};
use crate::{cavy_errors::ErrorBuf, num::Uint};
use crate::{interner_type, types::TypeSize};
use std::{collections::HashMap, fmt};

interner_type! { SymbolInterner : SymbolId -> String }

macro_rules! common_types {
    ($($ty:ident),*) => {
        pub struct CommonTypes {
            $(pub $ty: TyId),*
        }
    };
}

common_types! {
    unit, bool, u4, u8, u16, u32,
    q_bool, q_u4, q_u8, q_u16, q_u32,
    // This is a provisional type not intended to stay in the compiler forever
    ord
}

/// This is the big data structure that carries around all the data associated
/// with a compilation unit that may between compiler phases. Symbol tables,
/// arenas and interners, and so on, as well as notionally immutable
/// configuration data all live in here.
pub struct Context<'ctx> {
    /// The 'immutable' state associated with the compilation process
    pub conf: &'ctx Config,
    /// The source code used by the compiler
    pub srcs: SrcStore,
    /// Interned symbols
    pub symbols: SymbolInterner,
    /// Interned types
    pub types: CachedTypeInterner,
    /// Common types, made more conveniently accessible
    pub common: CommonTypes,
}

impl<'ctx> Context<'ctx> {
    pub fn new(conf: &'ctx Config) -> Self {
        let mut types = CachedTypeInterner::new();
        let common = CommonTypes {
            unit: types.intern(Type::unit()),
            bool: types.intern(Type::Bool),
            u4: types.intern(Type::Uint(Uint::U4)),
            u8: types.intern(Type::Uint(Uint::U8)),
            u16: types.intern(Type::Uint(Uint::U16)),
            u32: types.intern(Type::Uint(Uint::U32)),
            q_bool: types.intern(Type::Q_Bool),
            q_u4: types.intern(Type::Q_Uint(Uint::U4)),
            q_u8: types.intern(Type::Q_Uint(Uint::U8)),
            q_u16: types.intern(Type::Q_Uint(Uint::U16)),
            q_u32: types.intern(Type::Q_Uint(Uint::U32)),
            ord: types.intern(Type::Ord),
        };
        Self {
            conf,
            types,
            common,
            srcs: SrcStore::new(),
            symbols: SymbolInterner::new(),
        }
    }

    pub fn last_phase(&self) -> &Phase {
        &self.conf.phase_config.last_phase
    }

    pub fn intern_symb(&mut self, symb: String) -> SymbolId {
        self.symbols.intern(symb)
    }

    pub fn intern_ty(&mut self, ty: Type) -> TyId {
        self.types.intern(ty)
    }
}

/// A trait for formatting things with with the help of a `Context`
pub trait CtxDisplay {
    fn fmt_with<'t>(&'t self, ctx: &'t Context) -> CtxFmt<'t, Self>
    where
        Self: Sized,
    {
        CtxFmt { self_: self, ctx }
    }

    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

/// This struct is an implementation detail of the `CtxDisplay` trait
pub struct CtxFmt<'t, T: CtxDisplay> {
    self_: &'t T,
    ctx: &'t Context<'t>,
}

impl<'t, T: CtxDisplay> fmt::Display for CtxFmt<'t, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.self_.fmt(self.ctx, f)
    }
}

/// ====== Display and formatting ======

impl CtxDisplay for SymbolId {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ctx.symbols[*self])
    }
}
