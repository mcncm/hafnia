//! This module contains the compiler pass for lowering the AST to the CFG.

use crate::ast::AstCtx;
use crate::cfg::{Cfg, CfgCtx};
use crate::session::Session;
use crate::source::SrcStore;
use crate::types::TyStore;
use std::collections::HashMap;

pub fn lower(ast: AstCtx, sess: &Session) -> CfgCtx {
    let cfg = CfgCtx {
        store: HashMap::new(),
        types: TyStore::new(),
        entry_point: ast.entry_point,
    };

    cfg
}
