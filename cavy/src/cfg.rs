//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR. Like the MIR, it is a fully-typed version of the program, with
//! all names resolved.

use crate::ast::{AstCtx, FnId};
use crate::index_triple;
use crate::{
    num::Uint,
    types::{TyId, TyStore, Type},
};
use std::{collections::HashMap, env::args};

index_triple! { BlockStore : BlockId -> BasicBlock }
index_triple! { LocalStore : LocalId -> Local }

/// I'm not so sure that the `ctx` naming pattern makes very much sense here,
/// but we're provisionally sticking with the convention, I guess.
#[derive(Debug)]
pub struct Cfg {
    pub graphs: HashMap<FnId, Graph>,
    pub types: TyStore,
    pub entry_point: Option<FnId>,
}

impl Cfg {
    pub fn new(ast: &AstCtx) -> Self {
        Self {
            graphs: HashMap::with_capacity(ast.funcs.len()),
            types: TyStore::new(),
            entry_point: ast.entry_point,
        }
    }
}

/// A typed function signature
#[derive(Debug)]
pub struct TypedSig {
    /// Input parameters
    pub params: Vec<TyId>,
    /// Return type
    pub output: TyId,
}

/// The control-flow graph of a function
#[derive(Debug)]
pub struct Graph {
    /// The number of function arguments
    pub args: usize,
    /// The variables used within the CFG. This also contains the parameter and
    /// return values.
    pub locals: LocalStore,
    /// The basic blocks of the Cfg
    pub blocks: BlockStore,
    /// The first block of the Cfg
    pub entry_block: BlockId,
}

impl Graph {
    /// Create a graph with a single empty block
    pub fn new(TypedSig { params, output }: TypedSig) -> Self {
        let mut locals = LocalStore::new();
        let args = params.len();
        locals.insert(Local { ty: output });
        for param in params {
            locals.insert(Local { ty: param });
        }
        let mut blocks = BlockStore::new();
        let block = blocks.insert(BasicBlock::new());
        Self {
            args,
            locals,
            blocks,
            entry_block: block,
        }
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    stmts: Vec<Stmt>,
    kind: BlockKind,
}

impl BasicBlock {
    pub fn new() -> Self {
        Self {
            stmts: vec![],
            kind: BlockKind::Ret,
        }
    }
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
    pub ty: TyId,
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
