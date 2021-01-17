//! This module is home to the `Context` data structure central to the
//! compilation process.

use crate::cavy_errors::ErrorBuf;
use crate::interner_type;
use crate::session::Config;
use crate::session::Phase;
use crate::source::{SrcId, SrcStore};
use crate::types::{Type, TypeInterner};
use std::fmt;

interner_type! { SymbolInterner : SymbolId -> String }

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
    pub types: TypeInterner,
}

impl<'ctx> Context<'ctx> {
    pub fn new(conf: &'ctx Config) -> Self {
        Self {
            conf,
            srcs: SrcStore::new(),
            symbols: SymbolInterner::new(),
            types: TypeInterner::new(),
        }
    }

    pub fn last_phase(&self) -> &Phase {
        &self.conf.phase_config.last_phase
    }
}

/// A trait for formatting things with with the help of a `Context`
pub trait CtxFmt<'t, Fmt>
where
    Fmt: fmt::Display,
{
    fn fmt_with(&'t self, ctx: &'t Context) -> Fmt;
}
