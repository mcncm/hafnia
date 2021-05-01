//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR. Like the MIR, it is a fully-typed version of the program, with
//! all names resolved, and its structure is *very* similar. This module is
//! *essentially* a simplified version of `rustc_middle/src/mir/mod.rs`.

use crate::store_type;
use crate::{
    ast::{self, Ast, FnId},
    context::{Context, SymbolId},
    num::{self, Uint},
    source::Span,
    store::Store,
    types::{RefKind, TyId, Type},
    util::{FmtWith, FmtWrapper},
    values::Value,
};
use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    env::args,
    fmt,
    rc::Rc,
};

store_type! { BlockStore : BlockId -> BasicBlock }
store_type! { LocalStore : LocalId -> Local }

impl LocalStore {
    pub fn type_of(&self, place: &Place, ctx: &Context) -> TyId {
        let mut ty = self[place.root].ty;
        for elem in place.path.iter() {
            ty = ty.slot(*elem, ctx);
        }
        ty
    }
}

/// The whole-program middle intermediate representation.
#[derive(Debug)]
pub struct Mir {
    pub graphs: Store<FnId, Graph>,
    pub graph_data: Store<FnId, GraphData>,
    pub entry_point: Option<FnId>,
}

impl Mir {
    pub fn new(ast: &Ast) -> Self {
        Self {
            graphs: Store::with_capacity(ast.funcs.len()),
            graph_data: Store::with_capacity(ast.funcs.len()),
            entry_point: ast.entry_point,
        }
    }
}

/// Satellite data about a function: this will be the place to add visibility,
/// definition name, whether this is a closure, method, or regular `fn` item,
/// and so on.
#[derive(Debug)]
pub struct GraphData {
    pub is_unsafe: bool,
    pub is_rev: bool,
    pub def_name: SymbolId,
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

/// A precise position within the MIR control-flow graph
#[derive(Debug)]
pub struct GraphPosition {
    blk: BlockId,
    stmt: usize,
}

type Predecessors = Store<BlockId, Vec<BlockId>>;

/// A lazily-computed CFG predecessor graph. Like many other parts of the Mir,
/// this is basically the same as the data structure used by `rustc`. The
/// rational for using an outside store, rather than maintaining predecessors in
/// the blocks themselves, is that the effects of changing the out-pointers of a
/// block are essentially as nonlocal as possible. Any other blocks could have
/// their predecessors invalidated, but recomputing them from purely local data
/// is *also* finicky. This is just easier.
///
/// The only way it's really different from the `rustc` implementation is that it never
/// reallocates; this will use a little more space, but probably not too much,
/// and should be (slightly) faster.
struct PredGraph {
    /// The current predecessors graph.
    preds: RefCell<Store<BlockId, Vec<BlockId>>>,
    /// Has the current graph been invalidated?
    invalid: RefCell<bool>,
}

impl PredGraph {
    fn new() -> Self {
        Self {
            preds: RefCell::new(Store::new()),
            invalid: RefCell::new(true),
        }
    }

    /// Empty the store (lazily)
    fn invalidate(&mut self) {
        self.invalid.replace(true);
    }

    /// (Re)compute the predecessor graph using interior mutability
    fn compute(&self, blocks: &BlockStore) {
        let mut preds = self.preds.borrow_mut();
        for elem in preds.iter_mut() {
            elem.clear();
        }

        // Extend the graph if it isn't yet large enough. Is this slow?
        let diff = blocks.len() - preds.len();
        for _ in 0..diff {
            preds.insert(Vec::new());
        }

        for (idx, block) in blocks.idx_enumerate() {
            for succ in block.successors() {
                preds[idx].push(*succ);
            }
        }
        self.invalid.replace(false);
    }

    fn get_preds(&self, blocks: &BlockStore) -> Ref<Store<BlockId, Vec<BlockId>>> {
        if *self.invalid.borrow() {
            self.compute(blocks);
        }
        self.preds.borrow()
    }
}

pub struct GraphLoc {
    pub blk: BlockId,
    pub stmt: usize,
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
    /// The basic blocks of the CFG. Blocks can only be accessed through the
    /// `get_blk` and `get_blk_mut` methods.
    blocks: BlockStore,
    /// The first block of the CFG
    pub entry_block: BlockId,
    /// The final block of the CFG
    pub exit_block: BlockId,
    /// The predecessor graph
    preds: PredGraph,
}

impl Graph {
    /// Create a graph with a single empty block
    pub fn new(sig: &TypedSig) -> Self {
        let mut blocks = BlockStore::new();
        let entry_block = blocks.insert(BasicBlock::new());
        let exit_block = entry_block;
        let nargs = sig.params.len();
        Self {
            locals: LocalStore::new(),
            blocks,
            preds: PredGraph::new(),
            nargs,
            entry_block,
            exit_block,
        }
    }

    /// Get the number of basic blocks in the graph.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &BasicBlock> {
        self.blocks.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut BasicBlock> {
        self.blocks.iter_mut()
    }

    pub fn idx_enumerate(&self) -> impl Iterator<Item = (BlockId, &BasicBlock)> {
        self.blocks.idx_enumerate()
    }

    pub fn get_blocks(&self) -> &BlockStore {
        &self.blocks
    }

    pub fn get_preds(&self) -> Ref<Predecessors> {
        self.preds.get_preds(&self.blocks)
    }

    // NOTE: The *only* call site of this method is `GraphBuilder::new_block`.
    // That *should* use `Graph::new_block`, but it has to carry around all this
    // extra satellite data that I don't actually want to have.
    pub fn insert_block(&mut self, blk: BasicBlock) -> BlockId {
        self.blocks.insert(blk)
    }

    pub fn type_of(&self, place: &Place, ctx: &Context) -> TyId {
        self.locals.type_of(place, ctx)
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
        self.auto_local(ty).into()
    }

    pub fn user_place(&mut self, ty: TyId) -> Place {
        self.user_local(ty).into()
    }

    pub fn push_stmt(&mut self, block: BlockId, stmt: Stmt) {
        self.blocks[block].stmts.push(stmt)
    }
}

impl std::ops::Index<BlockId> for Graph {
    type Output = BasicBlock;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.blocks[index]
    }
}

impl std::ops::IndexMut<BlockId> for Graph {
    fn index_mut(&mut self, index: BlockId) -> &mut Self::Output {
        self.preds.invalidate();
        &mut self.blocks[index]
    }
}

/// Data about the scope in which some element is found. For now, this has only
/// very little data in it.
#[derive(Debug)]
pub struct ScopeData {
    pub in_unsafe: bool,
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

    pub fn successors(&self) -> &[BlockId] {
        self.kind.successors()
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
    /// lighter-weight alternative that could be used here? `smallvec` might be
    /// a good option.
    Switch { cond: Place, blks: Vec<BlockId> },
    /// A block ending in a function call
    Call(Box<FnCall>),
    /// A return
    Ret,
}

impl BlockKind {
    pub fn successors(&self) -> &[BlockId] {
        match &self {
            BlockKind::Goto(blk) => std::slice::from_ref(blk),
            BlockKind::Switch { blks, .. } => &blks,
            BlockKind::Call(call) => std::slice::from_ref(&call.blk),
            BlockKind::Ret => &[],
        }
    }
}

/// A CFG-level representation of a function call, which lives in a block tail
#[derive(Debug)]
pub struct FnCall {
    /// The function being called. This might not be the right type, in
    /// particular if we introduce closures or other "callables".
    pub callee: FnId,
    /// For now, this just says whether it's in an unsafe scope or not.
    pub scope_data: ScopeData,
    /// The span of the function call
    pub span: Span,
    pub args: Vec<Operand>,
    /// the place to which the function returns
    pub ret: Place,
    /// The block to which the function returns
    pub blk: BlockId,
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

/// As in rustc, a `Place` where data can be stored is a path rooted at a local
/// variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: LocalId,
    pub path: Vec<usize>,
}

impl Place {
    /// Check if this `Place` has a nonempty path, or the root of a local.
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }
}

impl From<LocalId> for Place {
    fn from(root: LocalId) -> Self {
        Self {
            root,
            path: Vec::new(),
        }
    }
}

/// For the time being, at least, lowered statements are *all* of the form `lhs
/// = rhs`.
#[derive(Debug)]
pub struct Stmt {
    pub span: Span,
    pub scope_data: ScopeData,
    pub kind: StmtKind,
}

impl Stmt {
    pub fn is_nop(&self) -> bool {
        // Or, could just derive `Eq`
        matches!(self.kind, StmtKind::Nop)
    }
}

#[derive(Debug)]
pub enum StmtKind {
    /// Assign an `Rvalue` to a local. In the future, this will support more
    /// complex left-hand sides.
    Assn(Place, Rvalue),
    /// (Unsafely) the state of a value (...as zero only, for now)
    Assert(Place),
    /// Drop a named variable
    Drop(Place),
    /// Read from or return a value to the host machine
    Io(IoStmtKind),
    /// Handy for deleting statements in O(1) time.
    Nop,
}

/// This exactly mirrors the same-named struct in the AST
#[derive(Debug)]
pub enum IoStmtKind {
    /// Input is not yet implemented
    In,
    Out {
        // Must be a place: can't meaningfully do I/O with a value known at
        // compile time. There's a reasonable case that someone could use the
        // `io` statement with a constant to test their setup, so this really
        // needs to work as expected.
        place: Place,
        symb: SymbolId,
    },
}

#[derive(Debug)]
pub struct Rvalue {
    pub data: RvalueKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum Operand {
    Const(Value),
    Copy(Place),
    Move(Place),
}

impl Operand {
    pub fn place(&self) -> Option<&Place> {
        match self {
            Self::Const(_) => None,
            Self::Copy(place) | Self::Move(place) => Some(place),
        }
    }

    pub fn unwrap_place(self) -> Place {
        match self {
            Self::Const(_) => panic!("expected a `Place`"),
            Self::Copy(place) | Self::Move(place) => place,
        }
    }
}

/// Find this in rustc mir.rs; see 'The MIR' in the rustc Dev Guide.
#[derive(Debug)]
pub enum RvalueKind {
    BinOp(BinOp, Operand, Operand),
    UnOp(UnOp, Operand),
    Ref(RefKind, Place),
    Use(Operand),
}

// Consider if you really want this alias, of if you ought to either lower the
// operators, or factor them out of ast, the way you have done with `num.rs`.
pub type BinOp = ast::BinOpKind;

pub type UnOp = ast::UnOpKind;

// ====== Display and formatting ======

impl fmt::Debug for PredGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("<predecessors graph>")
    }
}

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl<'c> FmtWith<Context<'c>> for Mir {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for gr in self.graphs.iter() {
            write!(f, "{}", gr.fmt_with(ctx))?;
        }
        Ok(())
    }
}

/// We need context data to format a `Graph` struct, at least to resolve the
/// types and symbols.
impl<'c> FmtWith<Context<'c>> for Graph {
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
            BlockKind::Call(call) => {
                write!(f, "{} = call {:?}(", call.ret, call.callee)?;
                call.args.iter().fold(true, |first, arg| {
                    if !first {
                        let _ = f.write_str(", ");
                    }
                    let _ = write!(f, "{}", arg);
                    false
                });
                write!(f, ") => {}", call.blk)
            }
            BlockKind::Ret => f.write_str("return;"),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StmtKind::Assn(place, rhs) => write!(f, "{} = {};", place, rhs),
            StmtKind::Assert(place) => write!(f, "assert {};", place),
            StmtKind::Drop(place) => write!(f, "assert {};", place),
            StmtKind::Io(io) => {
                match io {
                    IoStmtKind::In => unimplemented!(),
                    // Can't actually be formatted without Ctx
                    IoStmtKind::Out { place, symb } => {
                        write!(f, "io {:?}: {:?};", place, symb)
                    }
                }
            }
            StmtKind::Nop => f.write_str("nop;"),
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.root)?;
        for elem in self.path.iter() {
            write!(f, ".{}", elem)?;
        }
        Ok(())
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
            Self::Use(arg) => write!(f, "{}", arg),
            Self::Ref(ref_kind, place) => write!(f, "{}{}", ref_kind, place),
        }
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.data)
    }
}
