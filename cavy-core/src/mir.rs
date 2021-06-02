//! The control-flow graph representation of the program. This is analogous to
//! rustc's MIR. Like the rustc MIR, it is a fully-typed version of the program,
//! with all names fully resolved. Its structure is *very* similar. There's good
//! reason to use a simplified version of essentially the same CFG data
//! structure. Working backwards from the goal of implementing a borrow checker
//! similar to Rust's, it's sensible to operate over a similar domain, rather
//! than add the incidental complexity of translating from to another. Because
//! our surface syntax is also quite rusty, this entails good "impedance
//! matching" looking in the other direction, too.
//!
//! To compare these data structures with with the analogous ones in rustc, take
//! a look at the module in `rustc_middle/src/mir/mod.rs`.

use ast::IoDirection;
use smallvec::SmallVec;

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
        let ty = self[place.root].ty;
        ty.project(&place.path, ctx)
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

pub type Predecessors = Store<BlockId, Vec<BlockId>>;

/// A lazily-computed CFG predecessor graph. Like many other parts of the Mir,
/// this is basically the same as the data structure used by `rustc`. The
/// rationale for using an outside store, rather than maintaining predecessors in
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
    preds: RefCell<Predecessors>,
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

        // Extend the graph if it isn't yet large enough. (Is this slow?)
        // `saturating_sub`: if we ever remove blocks, `preds` will be longer
        // than the number of blocks.
        let diff = blocks.len().saturating_sub(preds.len());
        for _ in 0..diff {
            preds.insert(Vec::new());
        }

        for (idx, block) in blocks.idx_enumerate() {
            for succ in block.successors() {
                preds[*succ].push(idx);
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

/// A precise location within the control flow graph
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GraphPt {
    pub blk: BlockId,
    pub stmt: usize,
}

impl GraphPt {
    pub fn first(blk: BlockId) -> Self {
        Self { blk, stmt: 0 }
    }
}

/// The control-flow graph of a function
#[derive(Debug)]
pub struct Graph {
    /// The Id of the function this graph is lowered from
    pub id: FnId,
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
    pub fn new(id: FnId, sig: &TypedSig) -> Self {
        let mut blocks = BlockStore::new();
        let entry_block = blocks.insert(BasicBlock::new());
        let exit_block = entry_block;
        let nargs = sig.params.len();
        Self {
            id,
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

    pub fn get_blocks_mut(&mut self) -> &mut BlockStore {
        &mut self.blocks
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
    pub fn return_site() -> LocalId {
        LocalId::default()
    }

    pub fn new_block(&mut self) -> BlockId {
        self.blocks.insert(BasicBlock::new())
    }

    /// Creates a new GOTO block pointing at the argument
    pub fn goto_block(&mut self, block: BlockId) -> BlockId {
        self.blocks.insert(BasicBlock::goto(block))
    }

    pub fn new_local(&mut self, ty: TyId, kind: LocalKind) -> LocalId {
        let local = Local { ty, kind };
        self.locals.insert(local)
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
}

impl BasicBlock {
    pub fn new() -> Self {
        Self {
            stmts: vec![],
            kind: BlockKind::Ret,
        }
    }

    /// The length of this block, *including* its tail
    pub fn len(&self) -> usize {
        self.stmts.len() + 1
    }

    pub fn goto(block: BlockId) -> Self {
        Self {
            stmts: vec![],
            kind: BlockKind::Goto(block),
        }
    }

    pub fn successors(&self) -> &[BlockId] {
        self.kind.successors()
    }
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
    Switch(Box<Switch>),
    /// A block ending in a function call
    Call(Box<FnCall>),
    /// A return
    Ret,
}

impl BlockKind {
    pub fn successors(&self) -> &[BlockId] {
        match &self {
            BlockKind::Goto(blk) => std::slice::from_ref(blk),
            BlockKind::Switch(switch) => &switch.blks,
            BlockKind::Call(call) => std::slice::from_ref(&call.blk),
            BlockKind::Ret => &[],
        }
    }
}

#[derive(Debug)]
pub struct Switch {
    /// The guard expression
    pub cond: Place,
    /// The span thereof
    pub span: Span,
    /// The subsequent blocks; that is, the branches of the switch.
    pub blks: Vec<BlockId>,
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

#[derive(Debug, PartialEq, Eq)]
pub enum LocalKind {
    /// A temporary variable inserted by the compiler
    Auto,
    /// A user-defined variable, as in a `let` statement or function
    /// parameter.
    User,
    /// A variable visible to the caller: either an argument or a return site.
    Param,
}

/// As in rustc, a `Place` where data can be stored is a path rooted at a local
/// variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: LocalId,
    pub path: Vec<Proj>,
}

impl Place {
    /// Check if this `Place` has a nonempty path, or the root of a local.
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }

    pub fn len(&self) -> usize {
        self.path.len() + 1
    }

    /// Unlike in Rust, `Deref` projections don't actually refer to *different*
    /// memory locations, so it will often be useful to iterate over *just* the
    /// field projections, which represent actual memory offsets.
    pub fn iter_fields(&self) -> impl Iterator<Item = &usize> {
        self.path.iter().filter_map(|elem| elem.field_of())
    }

    /// Check if this is a prefix of another `Place`
    pub fn is_prefix(&self, other: &Place) -> bool {
        self.is_prefix_with(|_, _| true, other)
    }

    /// Check if this is a 'shallow prefix' of another `Place`; that is, it can
    /// be formed by removing elements that are not dereferences.
    pub fn is_shallow_prefix(&self, other: &Place) -> bool {
        self.is_prefix_with(|proj, in_self| in_self || proj != &Proj::Deref, other)
    }

    /// Check if this is a 'supporting prefix' of another `Place`; that is, it
    /// can be formed by removing elements that are not dereferences of a shared
    /// reference.
    ///
    /// See the NLL RFC at [Reborrow
    /// constraints](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#reborrow-constraints)
    pub fn is_supporting_prefix(&self, other: &Place, gr: &Graph, ctx: &Context) -> bool {
        let local = &gr.locals[other.root];
        // The type at the last-visited node of the path
        let mut ty = &ctx.types[local.ty];
        self.is_prefix_with(
            |proj, in_self| {
                if !in_self && (proj == &Proj::Deref) && matches!(ty, Type::Ref(RefKind::Shrd, _)) {
                    false
                } else {
                    ty = &ctx.types[ty.slot(proj)];
                    true
                }
            },
            other,
        )
    }

    /// Check if this is a prefix of another `Place`, and a predicate is
    /// satisfied at *all* points within the other `Place`.
    ///
    /// The predicate will take two arguments: the `Proj` from `other`, and a
    /// bool that is `true` if we are still within `self`.
    fn is_prefix_with<P>(&self, mut pred: P, other: &Place) -> bool
    where
        P: FnMut(&Proj, bool) -> bool,
    {
        // check prefixhood
        if self.root != other.root {
            return false;
        }

        let mut this = self.path.iter();
        let mut other = other.path.iter();
        while let Some(l) = this.next() {
            if !(other.next() == Some(l) && pred(l, true)) {
                return false;
            }
        }
        // and now check the rest of the other `Place`: if we are *above* any
        // satisfying place, we should test false.
        !other.any(|proj| pred(proj, false))
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

pub struct PlaceSlice<'p> {
    root: &'p LocalId,
    path: &'p [Proj],
}

/// A path element of a `Place`. Following `rustc`'s example, this can be either
/// a field access or a dereference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Proj {
    Field(usize),
    Deref,
}

impl Proj {
    /// If this projection is a field, return it.
    fn field_of(&self) -> Option<&usize> {
        match self {
            Proj::Field(field) => Some(field),
            Proj::Deref => None,
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
    Io(IoStmt),
    /// Handy for deleting statements in O(1) time.
    Nop,
}

/// This exactly mirrors the same-named struct in the AST
#[derive(Debug)]
pub struct IoStmt {
    pub place: Place,
    pub channel: SymbolId,
    pub dir: ast::IoDirection,
}

#[derive(Debug)]
pub struct Rvalue {
    pub data: RvalueKind,
    pub span: Span,
}

impl Rvalue {
    pub fn unit() -> Self {
        Rvalue {
            span: Span::default(), // FIXME always wrong
            data: RvalueKind::Use(Operand::Const(Value::Unit)),
        }
    }

    /// Get all the places read by the Rvalue
    pub fn places<'a>(&'a self) -> SmallVec<[&Place; 2]> {
        use RvalueKind::*;
        let mut places = SmallVec::new();
        let mut f = |op: &'a Operand| op.place().map(|pl| places.push(pl));
        // what a monstrosity
        match &self.data {
            BinOp(_, lop, rop) => {
                f(lop);
                f(rop);
            }
            UnOp(_, op) => {
                f(op);
            }
            Ref(_, pl) => places.push(pl),
            Use(op) => {
                f(op);
            }
            Array(items) => items.iter().for_each(|item| {
                f(item);
            }),
        };
        places
    }

    /// Get all the read by the Rvalue, mutably
    pub fn places_mut<'a>(&'a mut self) -> SmallVec<[&mut Place; 2]> {
        use RvalueKind::*;
        let mut places = SmallVec::new();
        let mut f = |op: &'a mut Operand| op.place_mut().map(|pl| places.push(pl));
        // what a monstrosity
        match &mut self.data {
            BinOp(_, lop, rop) => {
                f(lop);
                f(rop);
            }
            UnOp(_, op) => {
                f(op);
            }
            Ref(_, pl) => places.push(pl),
            Use(op) => {
                f(op);
            }
            Array(items) => items.iter_mut().for_each(|item| {
                f(item);
            }),
        };
        places
    }
}

#[derive(Debug, Clone)]
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

    pub fn place_mut(&mut self) -> Option<&mut Place> {
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
    /// The `rustc` mir has separate rvalue kinds for extensional and
    /// extensional arrays (`Aggregate`s and `Repeat`s, respectively). But we
    /// want to keep things nice and simple: we can spare the memory to desugar
    /// intensional arrays.
    Array(Vec<Operand>),
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
            BlockKind::Switch(switch) => {
                let cond = &switch.cond;
                let blks = &switch.blks;
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
            StmtKind::Drop(place) => write!(f, "drop {};", place),
            StmtKind::Io(io) => {
                match &io.dir {
                    IoDirection::In => unimplemented!(),
                    // Can't actually be formatted without Ctx
                    IoDirection::Out => {
                        write!(f, "io {:?}: {:?};", &io.place, io.channel)
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
            match elem {
                Proj::Field(field) => write!(f, ".{}", field)?,
                Proj::Deref => f.write_str(".*")?,
            };
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
            Self::Array(items) => {
                f.write_str("[")?;
                let mut items = items.iter();
                if let Some(head) = items.next() {
                    write!(f, "{}", head)?;
                }
                for item in items {
                    write!(f, ", {}", item)?;
                }
                f.write_str("]")
            }
        }
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl fmt::Debug for GraphPt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.blk, self.stmt)
    }
}
