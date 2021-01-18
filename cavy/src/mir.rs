//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR. Like the MIR, it is a fully-typed version of the program, with
//! all names resolved.

use crate::ast::{self, Ast, FnId};
// use crate::functions::{Func, UserFunc};
use crate::store_type;
use crate::{
    context::{Context, CtxFmt},
    num::{self, Uint},
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
        for (_fn_id, gr) in &self.mir.graphs {
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
    pub fn new() -> Self {
        let locals = LocalStore::new();
        let mut blocks = BlockStore::new();
        let entry_block = blocks.insert(BasicBlock::new());
        Self {
            locals,
            blocks,
            entry_block,
        }
    }

    /// The local corresponding to the routine's return value
    pub fn return_site(&self) -> LocalId {
        LocalId::default()
    }

    #[inline]
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
            for stmt in &block.stmts {
                let _ = writeln!(f, "\t\t{}", stmt);
            }
            let _ = f.write_str("\t}\n");
        }
        f.write_str("}\n")
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    pub stmts: Vec<Stmt>,
    pub kind: BlockKind,
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
pub enum BlockKind {
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

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            PlaceKind::Local(local) => write!(f, "{}", local),
            PlaceKind::Null => f.write_str("_"),
        }
    }
}

/// For the time being, at least, lowered statements are *all* of the form `lhs
/// = rhs`.
#[derive(Debug)]
pub struct Stmt {
    pub place: LocalId,
    pub rhs: Rvalue,
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {};", self.place, self.rhs)
    }
}

/// Find this in rustc mir.rs; see 'The MIR' in the rustc Dev Guide.
#[derive(Debug)]
pub enum Rvalue {
    BinOp(BinOp, Operand, Operand),
    UnOp(UnOp, Operand),
    Const(Const),
    Local(LocalId),
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BinOp(op, left, right) => write!(f, "{} {} {}", left, op, right),
            Self::UnOp(op, right) => write!(f, "{} {}", op, right),
            Self::Const(val) => write!(f, "{}", val),
            Self::Local(local) => write!(f, "{}", local),
        }
    }
}

// Consider if you really want this alias, of if you ought to either lower the
// operators, or factor them out of ast, the way you have done with `num.rs`.
pub type BinOp = ast::BinOpKind;

pub type UnOp = ast::UnOpKind;

/// Find this in rustc mir.rs; see 'The MIR' in the rustc Dev Guide.
#[derive(Debug)]
pub enum Operand {
    Const(Const),
    Copy(LocalId),
    Move(LocalId),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Const(val) => write!(f, "const {}", val),
            Self::Copy(local) => write!(f, "copy {}", local),
            Self::Move(local) => write!(f, "copy {}", local),
        }
    }
}

// This type is currently a *duplicate* of ast::LiteralKind.
#[derive(Debug)]
pub enum Const {
    False,
    True,
    Nat(num::NativeNum),
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::False => f.write_str("false"),
            Self::True => f.write_str("true"),
            Self::Nat(val) => write!(f, "{}", val),
        }
    }
}
