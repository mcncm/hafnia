//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR. Like the MIR, it is a fully-typed version of the program, with
//! all names resolved, and its structure is *very* similar. This module is
//! *essentially* a simplified version of `rustc_middle/src/mir/mod.rs`.

use crate::{
    ast::{self, Ast, FnId},
    context::CtxDisplay,
    source::Span,
    store::Store,
    values::Value,
};
// use crate::functions::{Func, UserFunc};
use crate::store_type;
use crate::{
    context::{Context, CtxFmt, SymbolId},
    num::{self, Uint},
    types::{TyId, Type},
};
use std::{collections::HashMap, env::args, fmt};

store_type! { BlockStore : BlockId -> BasicBlock }
store_type! { LocalStore : LocalId -> Local }

/// The whole-program middle intermediate representation.
#[derive(Debug)]
pub struct Mir {
    pub graphs: Store<FnId, Graph>,
    pub entry_point: Option<FnId>,
}

impl Mir {
    pub fn new(ast: &Ast) -> Self {
        Self {
            graphs: Store::with_capacity(ast.funcs.len()),
            entry_point: ast.entry_point,
        }
    }
}

/// A typed function signature
#[derive(Debug)]
pub struct TypedSig {
    /// Input parameters
    pub params: Vec<(SymbolId, TyId)>,
    /// Return type
    pub output: TyId,
    pub span: Span,
}

/// A fully-resolved position within the MIR control-flow graph
#[derive(Debug)]
pub struct GraphPosition {
    blk: BlockId,
    stmt: usize,
}

/// The control-flow graph of a function
#[derive(Debug)]
pub struct Graph {
    /// The variables used within the CFG. This also contains the parameter and
    /// return values.
    pub locals: LocalStore,
    /// The number of arguments. We don't need to pass in any more information
    /// than this, because we can rely on the invariant that the return site and
    /// arguments are the first `nargs + 1` locals.
    pub nargs: usize,
    /// The basic blocks of the Cfg
    pub blocks: BlockStore,
    /// The first block of the Cfg
    pub entry_block: BlockId,
}

impl Graph {
    /// Create a graph with a single empty block
    pub fn new(sig: &TypedSig) -> Self {
        let mut blocks = BlockStore::new();
        let entry_block = blocks.insert(BasicBlock::new());
        let nargs = sig.params.len();
        Self {
            locals: LocalStore::new(),
            blocks,
            nargs,
            entry_block,
        }
    }

    /// The local corresponding to the routine's return value
    pub fn return_site(&self) -> LocalId {
        LocalId::default()
    }

    pub fn new_block(&mut self) -> BlockId {
        self.blocks.insert(BasicBlock::new())
    }

    /// Creates a new GOTO block pointing at the argument
    pub fn goto_block(&mut self, block: BlockId) -> BlockId {
        self.blocks.insert(BasicBlock::goto(block))
    }

    fn alloc_new_local(&mut self, ty: TyId, kind: LocalKind) -> LocalId {
        let local = Local { ty, kind };
        self.locals.insert(local)
    }

    pub fn auto_local(&mut self, ty: TyId) -> LocalId {
        self.alloc_new_local(ty, LocalKind::Auto)
    }

    pub fn user_local(&mut self, ty: TyId) -> LocalId {
        self.alloc_new_local(ty, LocalKind::User)
    }

    pub fn auto_place(&mut self, ty: TyId) -> Place {
        Place {
            kind: PlaceKind::Local(self.auto_local(ty)),
        }
    }

    pub fn user_place(&mut self, ty: TyId) -> Place {
        Place {
            kind: PlaceKind::Local(self.user_local(ty)),
        }
    }

    pub fn push_stmt(&mut self, block: BlockId, stmt: Stmt) {
        self.blocks[block].stmts.push(stmt)
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    /// The branch-free sequence of MIR statements within the basic block
    pub stmts: Vec<Stmt>,
    /// The tail of the basic block, which may be of multiple kinds: a switch, a
    /// function call, and so on
    pub kind: BlockKind,
    /// Satellite data associated with this block, such as helpful precomputed
    /// facts about its position in the graph
    pub data: BlockData,
}

impl BasicBlock {
    pub fn new() -> Self {
        Self {
            stmts: vec![],
            kind: BlockKind::Ret,
            data: BlockData::default(),
        }
    }

    pub fn goto(block: BlockId) -> Self {
        Self {
            stmts: vec![],
            kind: BlockKind::Goto(block),
            data: BlockData::default(),
        }
    }
}

/// Satellite data associated with a basic block
#[derive(Debug, Clone, Default)]
pub struct BlockData {
    /// This extra datum contains the nearest enclosing branch, which may or may
    /// not be linear. It may not be strictly necessary to collect this data
    /// during graph building and maintain it throughout the lifecycle of the
    /// mir, but it will otherwise be computed during code generation and
    /// possibly multiple analyses.
    pub sup_branch: Option<BlockId>,
    /// The nearest enclosing *linear* branch. This is used for some analyses.
    pub sup_lin_branch: Option<BlockId>,
}

/// This specifies where the block points to next: either it
#[derive(Debug)]
pub enum BlockKind {
    /// This connects directly into another basic block (implying that this
    /// block has at least two parents)
    Goto(BlockId),
    /// An n-way conditional jump.
    ///
    /// NOTE: this vec will *almost always* have only two elements. Is there a
    /// lighter-weight alternative that could be used here? Smallvec might be an
    /// option.
    Switch { cond: LocalId, blks: Vec<BlockId> },
    /// A block ending in a function call
    Call {
        /// The function being called. This might not be the right type, in
        /// particular if we introduce closures or other "callables".
        callee: FnId,
        /// The span of the function call
        span: Span,
        args: Vec<Operand>,
        /// The block to which the function returns
        blk: BlockId,
    },
    /// A return
    Ret,
}

#[derive(Debug)]
pub struct Local {
    pub ty: TyId,
    pub kind: LocalKind,
}

#[derive(Debug)]
pub enum LocalKind {
    /// A temporary variable inserted by the compiler
    Auto,
    /// A user-defined variable, as a in a `let` statement or function
    /// parameter.
    User,
}

#[derive(Debug)]
pub struct Place {
    pub kind: PlaceKind,
}

#[derive(Debug)]
pub enum PlaceKind {
    /// A local variable: a temporary or a user-defined variable.
    Local(LocalId),
    /// The memory hole
    Null,
}

/// For the time being, at least, lowered statements are *all* of the form `lhs
/// = rhs`.
#[derive(Debug)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

#[derive(Debug)]
pub enum StmtKind {
    /// Assign an `Rvalue` to a local. In the future, this will support more
    /// complex left-hand sides.
    Assn(LocalId, Rvalue),
    /// Handy for deleting statements in O(1) time.
    Nop,
}

#[derive(Debug)]
pub struct Rvalue {
    pub data: RvalueKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum Operand {
    Const(Value),
    Copy(LocalId),
    Move(LocalId),
}

/// Find this in rustc mir.rs; see 'The MIR' in the rustc Dev Guide.
#[derive(Debug)]
pub enum RvalueKind {
    BinOp(BinOp, Operand, Operand),
    UnOp(UnOp, Operand),
    Use(Operand),
}

// Consider if you really want this alias, of if you ought to either lower the
// operators, or factor them out of ast, the way you have done with `num.rs`.
pub type BinOp = ast::BinOpKind;

pub type UnOp = ast::UnOpKind;

// ====== Display and formatting ======

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl CtxDisplay for Mir {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for gr in self.graphs.iter() {
            write!(f, "{}", gr.fmt_with(ctx))?;
        }
        f.write_str("")
    }
}

/// We need context data to format a `Graph` struct, at least to resolve the
/// types and symbols.
impl CtxDisplay for Graph {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _ = f.write_str("function {\n");
        for (n, local) in self.locals.iter().enumerate() {
            writeln!(f, "\t_{}: {}", n, local.ty.fmt_with(ctx))?;
        }

        for (n, block) in self.blocks.iter().enumerate() {
            writeln!(f, "\tbb{} {{", n)?;
            for stmt in &block.stmts {
                writeln!(f, "\t\t{}", stmt)?;
            }
            writeln!(f, "\t\t{}", block.kind)?;
            f.write_str("\t}\n")?;
        }
        f.write_str("}\n")
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl fmt::Display for BlockKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // These comma-separated lists are getting redundant. Consider how best
        // to abstract this pattern.
        match self {
            BlockKind::Goto(block) => write!(f, "goto [() => {}];", block),
            BlockKind::Switch { cond, blks } => {
                write!(f, "switch({}) [", cond)?;
                blks.iter().enumerate().fold(true, |first, (n, blk)| {
                    if !first {
                        let _ = f.write_str(", ");
                    }
                    let _ = write!(f, "{} => {}", n, blk);
                    false
                });
                f.write_str("];")
            }
            BlockKind::Call {
                callee,
                args,
                blk,
                span: _,
            } => {
                write!(f, "call {:?}(", callee)?;
                args.iter().fold(true, |first, arg| {
                    if !first {
                        let _ = f.write_str(", ");
                    }
                    let _ = write!(f, "{}", arg);
                    false
                });
                write!(f, ") => {}", blk)
            }
            BlockKind::Ret => f.write_str("return;"),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StmtKind::Assn(place, rhs) => write!(f, "{} = {};", place, rhs),
            StmtKind::Nop => f.write_str("nop;"),
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            PlaceKind::Local(local) => write!(f, "{}", local),
            PlaceKind::Null => f.write_str("_"),
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Const(c) => write!(f, "{}", c),
            Operand::Copy(x) => write!(f, "copy {}", x),
            Operand::Move(x) => write!(f, "move {}", x),
        }
    }
}

impl fmt::Display for RvalueKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BinOp(op, left, right) => write!(f, "{} {} {}", left, op, right),
            Self::UnOp(op, right) => write!(f, "{} {}", op, right),
            RvalueKind::Use(arg) => write!(f, "{}", arg),
        }
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.data)
    }
}
