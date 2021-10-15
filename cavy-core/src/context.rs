//! This module is home to the `Context` data structure central to the
//! compilation process.

use crate::types::{CachedTypeInterner, TyId, Type};
use crate::{cavy_errors::ErrorBuf, num::Uint};
use crate::{interner_type, types::TypeSize};
use crate::{
    session::{Config, Phase, Statistics},
    util::FmtWith,
};
use crate::{
    source::{SrcId, SrcStore},
    types::RefKind,
};
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
    unit, bool, u2, u4, u8, u16, u32,
    qbool, qu2, qu4, qu8, qu16, qu32,
    shrd_qbool,
    // This is a provisional type not intended to stay in the compiler forever
    ord
}

/// This is the big data structure that carries around all the data associated
/// with a compilation unit that may between compiler phases. Symbol tables,
/// arenas and interners, and so on, as well as notionally immutable
/// configuration data all live in here.
pub struct Context<'ctx> {
    /// Compiler performance data, etc.
    pub stats: &'ctx mut Statistics,
    /// The immutable state associated with the compilation process
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
    pub fn new(conf: &'ctx Config, stats: &'ctx mut Statistics) -> Self {
        let mut types = CachedTypeInterner::new();
        let qbool = types.intern(Type::QBool);
        let common = CommonTypes {
            unit: types.intern(Type::unit()),
            bool: types.intern(Type::Bool),
            u2: types.intern(Type::Uint(Uint::U2)),
            u4: types.intern(Type::Uint(Uint::U4)),
            u8: types.intern(Type::Uint(Uint::U8)),
            u16: types.intern(Type::Uint(Uint::U16)),
            u32: types.intern(Type::Uint(Uint::U32)),
            qbool,
            qu2: types.intern(Type::QUint(Uint::U2)),
            qu4: types.intern(Type::QUint(Uint::U4)),
            qu8: types.intern(Type::QUint(Uint::U8)),
            qu16: types.intern(Type::QUint(Uint::U16)),
            qu32: types.intern(Type::QUint(Uint::U32)),
            shrd_qbool: types.intern(Type::Ref(RefKind::Shrd, qbool)),
            ord: types.intern(Type::Ord),
        };
        Self {
            conf,
            stats,
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

// === A handy macro for creating a Context struct ===

/// Because you can't write a function of type `() -> Context`, but we sometimes
/// would like to get one from nowhere without remembering the incantation, this
/// macro automates the process of making a "default" context
#[macro_export]
macro_rules! default_context {
    ($name:ident) => {
        let mut stats = $crate::session::Statistics::new();
        let conf = $crate::session::Config::default();
        let mut $name = $crate::context::Context::new(&conf, &mut stats);
    };
}

// === Display and formatting ===

impl<'c> FmtWith<Context<'c>> for SymbolId {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ctx.symbols[*self])
    }
}
