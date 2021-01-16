//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR. Like the MIR, it is a fully-typed version of the program, with
//! all names resolved.

use crate::ast::{Ast, FnId};
use crate::store_type;
use crate::{
    context::{Context, CtxFmt},
    num::Uint,
    types::{TyId, Type},
};
use std::{collections::HashMap, env::args, fmt};

store_type! { BlockStore : BlockId -> BasicBlock }
store_type! { LocalStore : LocalId -> Local }

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

/// The whole-program middle intermediate representation.
#[derive(Debug)]
pub struct Mir {
    pub graphs: HashMap<FnId, Graph>,
    pub entry_point: Option<FnId>,
}

impl Mir {
    pub fn new(ast: &Ast) -> Self {
        Self {
            graphs: HashMap::with_capacity(ast.funcs.len()),
            entry_point: ast.entry_point,
        }
    }
}

/// We need context data to format a `Mir` struct, at least to resolve the types
/// and symbols.
impl<'t> CtxFmt<'t, MirFmt<'t>> for Mir {
    fn fmt_with(&'t self, ctx: &'t Context) -> MirFmt<'t> {
        MirFmt { mir: self, ctx }
    }
}

/// A wrapper type for formatting Mir with a context.
pub struct MirFmt<'t> {
    mir: &'t Mir,
    ctx: &'t Context<'t>,
}

impl<'t> fmt::Display for MirFmt<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (fn_id, gr) in &self.mir.graphs {
            let _ = write!(f, "{}", gr.fmt_with(&self.ctx));
        }
        f.write_str("")
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

/// We need context data to format a `Graph` struct, at least to resolve the
/// types and symbols.
impl<'t> CtxFmt<'t, GraphFmt<'t>> for Graph {
    fn fmt_with(&'t self, ctx: &'t Context) -> GraphFmt<'t> {
        GraphFmt { gr: self, ctx }
    }
}

/// A wrapper type for formatting Mir with a context.
pub struct GraphFmt<'t> {
    pub gr: &'t Graph,
    pub ctx: &'t Context<'t>,
}

impl<'t> fmt::Display for GraphFmt<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _ = f.write_str("function {\n");
        for (n, local) in self.gr.locals.iter().enumerate() {
            let ty = &self.ctx.types[local.ty];
            let _ = writeln!(f, "\t_{}: {}", n, ty.fmt_with(self.ctx),);
        }

        for (n, block) in self.gr.blocks.iter().enumerate() {
            let _ = writeln!(f, "\tbb{} {{", n);
            let _ = f.write_str("\t\t// block contents\n\t}");
        }
        f.write_str("}\n")
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
