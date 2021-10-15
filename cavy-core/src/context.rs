//! This module is home to the `Context` data structure central to the
//! compilation process.

use crate::types::{TyId, Type, TypeInterner};
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

pub struct Prelude {
    pub types: HashMap<SymbolId, TyId>,
}

macro_rules! prelude_types {
    ($symbols:ident $($symb:expr => $ty:expr),*) => {
        {
            let mut prelude_types = HashMap::new();
            $(
                let symb = $symbols.intern($symb.to_owned());
                prelude_types.insert(symb, $ty);
            )*
            prelude_types
        }
    };
}

impl Prelude {
    fn new(symbols: &mut SymbolInterner, types: &TypeInterner) -> Self {
        let common = &types.common;
        let types = prelude_types! {
            symbols
            "bool"  => common.bool,
            "u2"    => common.u2,
            "u4"    => common.u4,
            "u8"    => common.u8,
            "u16"   => common.u16,
            "u32"   => common.u32,
            "qbool" => common.qbool,
            "qu2"   => common.qu2,
            "qu4"   => common.qu4,
            "qu8"   => common.qu8,
            "qu16"  => common.qu16,
            "qu32"  => common.qu32
        };
        Self { types }
    }
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
    pub types: TypeInterner,
    /// Names automatically brought into scope
    pub prelude: Prelude,
}

struct CommonType {
    symbol: Option<SymbolId>,
    ty: TyId,
}

impl<'ctx> Context<'ctx> {
    pub fn new(conf: &'ctx Config, stats: &'ctx mut Statistics) -> Self {
        let types = TypeInterner::new();
        let mut symbols = SymbolInterner::new();
        let prelude = Prelude::new(&mut symbols, &types);
        Self {
            conf,
            stats,
            srcs: SrcStore::new(),
            symbols,
            types,
            prelude,
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
