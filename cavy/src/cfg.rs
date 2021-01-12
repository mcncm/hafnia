//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR.

use crate::ast::FnId;
use crate::index_triple;
use crate::types::{TyId, TyStore, Type};
use std::collections::HashMap;

index_triple! { BlockStore : BlockId -> BasicBlock }
index_triple! { LocalStore : LocalId -> Local }

/// I'm not so sure that the `ctx` naming pattern makes very much sense here,
/// but we're provisionally sticking with the convention, I guess.
#[derive(Debug)]
pub struct CfgCtx {
    pub store: HashMap<FnId, Cfg>,
    pub types: TyStore,
    pub entry_point: Option<FnId>,
}

/// The control-flow graph of a single function
#[derive(Debug)]
pub struct Cfg {
    /// The number of function arguments
    pub args: usize,
    /// The variables used within the CFG
    pub locals: LocalStore,
    /// The basic blocks of the Cfg
    pub blocks: BlockStore,
    /// The first block of the Cfg
    pub entry_block: BlockId,
}

#[derive(Debug)]
pub struct BasicBlock {
    stmts: Vec<Stmt>,
    kind: BlockKind,
}

/// This specifies where the block points to next: either it
#[derive(Debug)]
enum BlockKind {
    /// This connects directly into another basic block (implying that this
    /// block has at least two parents)
    Goto(BlockId),
    /// A conditional with direct and indirect branches
    If {
        /// The direct branch
        dir: BlockId,
        /// The indirect branch
        ind: Option<BlockId>,
    },
    /// A return,
    Ret,
}

#[derive(Debug)]
pub struct Local {
    pub ty: Type,
}

#[derive(Debug)]
struct Stmt {
    lhs: Local,
    rhs: Rvalue,
}

/// Find this in rustc mir.rs; see 'The MIR' in the rustc Dev Guide.
#[derive(Debug)]
enum Rvalue {
    BinOp(BinOp, Operand, Operand),
    UnOp(UnOp, Operand),
    Place,
}

#[derive(Debug)]
enum BinOp {
    Plus,
}

#[derive(Debug)]
enum UnOp {
    Not,
}

/// Find this in rustc mir.rs; see 'The MIR' in the rustc Dev Guide.
#[derive(Debug)]
enum Operand {
    Const,
    Copy(Local),
    Move(Local),
}
