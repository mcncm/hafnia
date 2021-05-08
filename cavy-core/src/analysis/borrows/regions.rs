use std::fmt;

use crate::{mir::*, store::Store, store_type, types::RefKind, util::FmtWith};

use bitvec::prelude::*;

use super::{
    super::{graph, DataflowCtx, DataflowRunner},
    ascription::{self, Ascr, AscrNode, AscriptionStore},
    liveness::{self, LiveVars},
    util,
};

/// Main entry point for region inference
pub fn infer_regions<'a>(context: &'a DataflowCtx<'a>) -> RegionInf<'a> {
    let mut lifetimes = LifetimeStore::new();
    let ascriptions = ascription::ascribe(&mut lifetimes, &context);

    let liveness_ana = liveness::LivenessAnalysis::new(context.gr);
    let liveness = DataflowRunner::new(liveness_ana, &context)
        .run()
        .stmt_states;

    let mut reginf = RegionInf {
        lifetimes,
        ascriptions,
        liveness,
        context,
        constraints: Constraints::new(),
    };

    reginf.collect_constraints();
    reginf.solve_constraints();

    // finally, return the data computed in this phase, to use it for borrow
    // checking and error reporting.
    reginf
}

// A map from lightweight lifetime variables to the regions they represent
store_type! { LifetimeStore : LtId -> Lifetime }

/// See [Named
/// lifetimes](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#layer-4-named-lifetimes):
/// this is exactly the data structure j
pub struct Lifetime {
    /// The "finite" points within the graph
    pts: Store<BlockId, BitVec>,
    /// The "points at infinity" in the caller. For now, we're making the
    /// simplifying assumption that there is a single such point; that is, that
    /// all function arguments and return values have the *same* lifetime. This
    /// bit is set if this lifetime extends to infinity.
    end: bool,
}

impl Lifetime {
    /// Add a single point to the lifetime
    pub fn insert(&mut self, pt: GraphPt) {
        let block = &mut self.pts[pt.blk];
        block.set(pt.stmt, true);
    }

    pub fn iter(&self) -> impl Iterator<Item = GraphPt> + '_ {
        self.pts
            .idx_enumerate()
            .map(move |(blk, stmts)| {
                stmts.iter().enumerate().filter_map(move |(stmt, bit)| {
                    if *bit {
                        Some(GraphPt { blk, stmt })
                    } else {
                        None
                    }
                })
            })
            .flatten()
    }

    pub fn contains(&self, pt: &GraphPt) -> bool {
        self.pts[pt.blk][pt.stmt]
    }
}

impl LifetimeStore {
    /// Construct an empty lifetime
    pub fn new_region(&mut self, block_sizes: &[usize]) -> LtId {
        let lifetime = Lifetime {
            pts: block_sizes.iter().map(|sz| bitvec![0; *sz]).collect(),
            end: false,
        };
        self.insert(lifetime)
    }

    /// Construct a lifetime that extends into the caller
    pub fn end_region(&mut self, block_sizes: &[usize]) -> LtId {
        let lifetime = Lifetime {
            pts: block_sizes.iter().map(|sz| bitvec![1; *sz]).collect(),
            end: true,
        };
        self.insert(lifetime)
    }
}

/// This struct does region inference to compute lifetimes.
pub struct RegionInf<'a> {
    pub lifetimes: LifetimeStore,
    pub ascriptions: AscriptionStore<'a>,
    pub liveness: Store<BlockId, Vec<LiveVars>>,
    context: &'a DataflowCtx<'a>,
    constraints: Constraints,
}

struct Constraints {
    constrs: Vec<OutlivesAt>,
}

/// A proposition that holds at a point
#[derive(Clone)]
struct LocalP<P> {
    pub prop: P,
    pub pt: GraphPt,
}

/// The lifetime subtype constraint representation described in `#Lifetime
/// inference constraints` of the NLL RFC.
#[derive(Clone)]
struct OutlivesP {
    pub long: LtId,
    pub shrt: LtId,
}

type OutlivesAt = LocalP<OutlivesP>;

/// A liveness constraint. This struct isn't *used* for much--it's entered
/// straight into the lifetime set--but it is useful to keep around for its
/// `Debug` implementation.
struct LiveP(LtId);

type LiveAt = LocalP<LiveP>;

impl<'a> RegionInf<'a> {
    fn collect_constraints(&mut self) {
        self.collect_liveness_constraints();
        self.collect_subtyping_constraints();
        self.collect_reborrow_constraints();
    }

    /// The liveness constraints are never collected into `Self::constraints`;
    /// they're just entered directly into each lifetime.
    ///
    /// See [Liveness](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#liveness)
    fn collect_liveness_constraints(&mut self) {
        // Iterate over the graph in *any* order; we're only entering
        // statement-local data here
        for pt in self.context.iter_pts() {
            // For now, working at the variable granularity.
            for var in self.liveness[pt].iter() {
                for ascr in self.ascriptions.local_ascriptions(var) {
                    self.lifetimes[ascr.lt].insert(pt);
                }
            }
        }
    }

    /// This one is a little bit subtler because, while `&` is covariant, `&mut`
    /// is *invariant*. In order to save ourselves some time before the upcoming
    /// deadline, we've used *separate* data structures for types and lifetimes.
    /// This means that enforcing the variance rules may become fragile: we need
    /// to take care here.
    ///
    /// See [Subtyping](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#subtyping)
    fn collect_subtyping_constraints(&mut self) {
        for (pt, stmt) in util::enumerate_stmts(self.context.gr) {
            // The constraint must take effect in the *next* statement. Because
            // we are not in a tail block, this is always safe.
            let mut nxt = pt;
            nxt.stmt += 1;

            let (lhs, rvalue) = match &stmt.kind {
                StmtKind::Assn(lhs, Rvalue { data: rvalue, .. }) => (lhs, rvalue),
                // only assignments (and calls) should generate subtyping constraints
                _ => return,
            };

            match rvalue {
                RvalueKind::BinOp(_, lop, rop) => {
                    self.sub_constr_oper(nxt, lhs, lop);
                    self.sub_constr_oper(nxt, lhs, rop);
                }
                RvalueKind::UnOp(_, op) | RvalueKind::Use(op) => {
                    self.sub_constr_oper(nxt, lhs, op);
                }
                RvalueKind::Ref(refr, place) => {
                    // Prefer if this weren't here; it's a hopeless tangle.
                    let ascr = self
                        .ascriptions
                        .get_ref(&pt)
                        .expect("loan was not ascribed")
                        .ascr
                        .clone();
                    debug_assert_eq!(&ascr.kind, refr);
                    self.sub_constr_loan(nxt, lhs, ascr, place);
                }
            };
        }

        // We also need to collect constraints from the block tails: they
        // matters too, because assignments happen in them!
        for (pt, tail) in util::enumerate_tails(self.context.gr) {
            match tail {
                BlockKind::Goto(_) => {}
                // NOTE: unlike Rust, we might actually need some special
                // treatment for this case, because the guard needs to live
                // until the end of the conditional.
                BlockKind::Switch { .. } => {}
                // NOTE: here we have to identify *which* lifetime the return
                // value has. For the time being, we're somewhat punting on this
                // problem, and treating all lifetimes in a function signature
                // as equal.
                BlockKind::Call(call) => {
                    let FnCall {
                        callee: _,
                        ref args,
                        ref ret,
                        ..
                    } = **call;
                    for arg in args {
                        // Here, we *do* need to look forward into the
                        // next block(s) to get the point(s) to insert the statement.
                        for &blk in self.context.gr[pt.blk].successors() {
                            let pt = GraphPt::first(blk);
                            self.sub_constr_oper(pt, ret, arg);
                        }
                    }
                }
                BlockKind::Ret => {}
            }
        }
    }

    fn sub_constr_oper(&mut self, pt: GraphPt, lhs: &Place, rhs: &Operand) {
        if let Some(rhs) = rhs.place() {
            self.sub_constr(pt, lhs, rhs);
        }
    }

    fn sub_constr(&mut self, pt: GraphPt, lhs: &Place, rhs: &Place) {
        // This is the crux of the subtyping constraints. We need to enforce the
        // covariance of shared references and invariance of unique references.
        match (
            &self.ascriptions.locals[lhs.root],
            &self.ascriptions.locals[rhs.root],
        ) {
            (Some(ltree), Some(rtree)) => {
                // Recursively apply the subtyping rule, with `rtree <: ltree`,
                // from the *next* point, which is where the constraint takes effect.
                self.constraints.insert_sub_constr(pt, rtree, ltree);
            }
            (None, None) => {}
            _ => {
                dbg!(
                    &self.ascriptions.locals[lhs.root],
                    &self.ascriptions.locals[rhs.root],
                );
                unreachable!("inconsistent ascriptions")
            }
        }
    }

    /// Insert a constraint from a borrow statement. This method is analogous to
    /// `Self::sub_constr`, except that the sides are "unbalanced", so we have
    /// to manually insert one level of constraint before entering the
    /// `Constraints::insert_sub_constr_{..}` recursive pair.
    fn sub_constr_loan(&mut self, pt: GraphPt, lhs: &Place, ascr: Ascr, rhs_inner: &Place) {
        let ltree = self.ascriptions.locals[lhs.root]
            .as_ref()
            .expect("lhs of borrow must have a lifetime");
        let shrt = ltree
            .this
            .as_ref()
            .expect("lhs must have a root-level ascription");

        // insert the constraint at the unbalanced level
        // FIXME: this fails to enforce `&mut`'s invariance
        self.constraints.outlives_from(ascr.lt, shrt.lt, pt);

        // finally, recurse on any contained types
        debug_assert_eq!(ltree.slots.len(), 1);
        match (
            ltree.slots[0].as_ref(),
            self.ascriptions.locals[rhs_inner.root].as_ref(),
        ) {
            (Some(ltree), Some(rtree)) => {
                self.constraints
                    .insert_sub_constr_inner(Some(ascr.kind), pt, rtree, ltree);
            }
            (None, None) => {}
            _ => unreachable!("lhs and rhs ascription trees differ"),
        }
    }

    /// See [Reborrow
    /// Constriants](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#reborrow-constraints)
    fn collect_reborrow_constraints(&mut self) {}

    /*
    Now comes constraint solving, in which we extend the lifetimes of subtypes
    (which should be longer) to those of their supertypes (which should be
    shorter; that is, less specialized, and therefore less useful).

    Following the RFC, we'll first do this by the most naive-possible loop over
    constraints. We'll repeatedly extend the subtype of each constraint `('a:
    'b) @ P` until no constraint changes any further. A subtype will be extended
    by DFS over the control-flow graph, exiting whenever we leave the shorter
    lifetime.

    Later, once we get this working, we can optimize the algorithm by adding a
    worklist, and so on.
    */

    /// See [Solving
    /// constraints](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#solving-constraints)
    fn solve_constraints(&mut self) {
        while self.extend_constraints() {}
    }

    /// Extend the inferior lifetime in each constraint; return `true` if any changed
    fn extend_constraints(&mut self) -> bool {
        let lifetimes = &mut self.lifetimes;
        let gr = &self.context.gr;
        self.constraints
            .iter()
            .map(|constr| {
                let long = constr.prop.long;
                let shrt = constr.prop.shrt;
                // Return early: this constraint is a no-op. We could opt not to
                // even insert these constraints, but this early-return establishes
                // the safety of the following line *locally*.
                if shrt == long {
                    return false;
                }

                // Safety: if the two lifetimes are identical, we have already returned.
                let (long, shrt) = unsafe { lifetimes.get_two_unchecked_mut(long, shrt) };

                long.extend_to(shrt, constr.pt, gr)
            })
            .any(|x| x)
    }
}

impl Constraints {
    fn new() -> Self {
        Self {
            constrs: Vec::new(),
        }
    }

    /// Apply the subtyping rule for `shrt <: long`
    fn insert_sub_constr(&mut self, pt: GraphPt, shrt: &AscrNode, long: &AscrNode) {
        match (&shrt.this, &long.this) {
            (
                Some(Ascr {
                    kind: shrt_kind,
                    lt: shrt_lt,
                }),
                Some(Ascr {
                    kind: long_kind,
                    lt: long_lt,
                }),
                // NOTE: it is *not* the case that `&mut T <: &T`. The former is
                // *coercible* to the latter, but it is not a subtype; if it
                // were, you could break all the rules.
            ) if shrt_kind == long_kind => {
                // insert the constraints at this level
                self.outlives_from(*long_lt, *shrt_lt, pt);

                // finally, recurse on any inner types that have lifetime
                // ascriptions
                self.insert_sub_constr_inner(Some(*shrt_kind), pt, shrt, long);
            }
            (None, None) => {
                /*
                recurse without any this-level constraints

                NOTE: this unconditional recursion isn't doing lots of extra
                work, and doesn't need to be memoized, because the ascription tree
                terminates at types containing no lifetimes.
                */

                self.insert_sub_constr_inner(None, pt, shrt, long);
            }
            _ => unreachable!("ascription or typechecker bug"),
        }
    }

    /// Recursively apply the subtyping rules to any *contained* types of
    fn insert_sub_constr_inner(
        &mut self,
        ref_kind: Option<RefKind>,
        pt: GraphPt,
        shrt: &AscrNode,
        long: &AscrNode,
    ) {
        let children = shrt
            .slots
            .iter()
            .zip(long.slots.iter())
            .filter_map(|(shrt, long)| match (shrt, long) {
                (Some(shrt), Some(long)) => Some((shrt, long)),
                (None, None) => None,
                _ => unreachable!("ascription or typechecker bug"),
            });
        for (short_chld, long_chld) in children {
            /*
            NOTE: this is the only place where variance rules are applied.
            */

            // unconditionally recurse *covariantly*:
            self.insert_sub_constr(pt, short_chld, long_chld);
            // recurse *contravariantly* if uniq ref
            if let Some(RefKind::Uniq) = ref_kind {
                self.insert_sub_constr(pt, long_chld, short_chld);
            }
        }
    }

    fn outlives_from(&mut self, long: LtId, shrt: LtId, pt: GraphPt) {
        self.constrs.push(LocalP {
            prop: OutlivesP { long, shrt },
            pt,
        });
    }
}

impl Lifetime {
    /// Minimally extend a lifetime to another one, starting from a given graph
    /// point. Return `true` if changed.
    fn extend_to(&mut self, other: &Lifetime, pt: GraphPt, gr: &Graph) -> bool {
        let mut changed = false;
        let mut stmt = pt.stmt; // starts at a nonzero value!
        let mut blocks = vec![pt.blk];
        while let Some(blk) = blocks.pop() {
            let this = &mut self[blk][stmt..];
            let other = &other[blk][stmt..];
            // NOTE: should be `other.leading_ones()`, but there seems to be a
            // bug in the `bitvec` crate.
            let mask = other.first_zero().unwrap_or_else(|| this.len());

            let ones = this.count_ones();
            // Add the other lifetime's points
            this[..mask].set_all(true);
            // Mark whether we got new points
            changed |= ones != this.count_ones();

            // End when we go out of the other lifetime
            if other.first_zero().is_some() {
                stmt = 0;
                continue;
            }

            // Otherwise, move on to the next blocks!
            blocks.extend(gr[blk].successors());
            // In all blocks but the first, start at the first statement.
            stmt = 0;
        }
        changed
    }
}

// === syntax for subtyping ===

/// A macro to add a constraint. I want to use this instead of a method for a
/// few reasons: first, with a method it's easier to get the order of the sub-
/// and supertypes backwards. Second, it would be possible to make it "generic"
/// over all kinds of constraints. Finally, it looks extremely cool.
/// Unfortunately, there's no `lvalue` fragment specifier, and it's unpleasant
/// and time-consuming to fake one by hand. Could accomplish this with a proc
/// macro.
#[cfg(any())] // do not compile
macro_rules! constr {
    ($constrs:expr |- $long:ident : $shrt:ident @ $pt:ident) => {
        $constrs.constrs.push(LocalP {
            prop: OutlivesP { long: $long, $shrt },
            pt,
        });
    };
}

// === boilerplate impls ===

impl Constraints {
    fn iter(&self) -> impl Iterator<Item = &OutlivesAt> {
        self.constrs.iter()
    }
}

impl fmt::Display for OutlivesP {
    /// Exact format from NLL RFC: `('foo: 'p) @ A/1`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}: {})", self.long, self.shrt)
    }
}

impl<T> fmt::Display for LocalP<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {:?}", self.prop, self.pt)
    }
}

impl fmt::Display for LiveAt {
    /// Exact format from NLL RFC: `('p: {A/1}) @ A/1`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}: {{{:?}}}) @ {:?}", self.prop.0, self.pt, self.pt)
    }
}

impl FmtWith<LifetimeStore> for LtId {
    fn fmt(&self, store: &LifetimeStore, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lifetime = &store[*self];
        for pt in lifetime.iter() {
            let constr = LiveAt {
                prop: LiveP(*self),
                pt,
            };
            writeln!(f, "{}", constr)?;
        }
        Ok(())
    }
}

impl std::ops::Index<BlockId> for Lifetime {
    type Output = BitVec;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.pts[index]
    }
}

impl std::ops::IndexMut<BlockId> for Lifetime {
    fn index_mut(&mut self, index: BlockId) -> &mut Self::Output {
        &mut self.pts[index]
    }
}

impl fmt::Display for LtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", self.0)
    }
}

/// Some debugging tools
#[cfg(debug_assertions)]
mod dbg {
    use crate::store::BitSet;

    use super::*;

    // Zip an arbitrary number of iterators
    macro_rules! nzip {
        ($z:expr) => { $z };
        ($s:expr, $($n:expr),+) => {
            ($s).zip(nzip!($($n),+))
        };
    }

    // Write an unzip binding expression like `(x, (y, z))`
    macro_rules! unzip_bind {
        ( $z:ident ) => { $z };
        ( $sz:ident, $z:ident ) => { ($sz, $z) };
        ( $s:ident, $($n:ident),+ ) => {
            ($s, unzip_bind!($($n),+))
        };
    }

    macro_rules! table_fmtter {
        ($width:expr; $col:ident[$colw:expr]) => {
            table_fmtter!($colw; $col)
        };
        ($width:expr; $col:expr) => {
            concat!("{:", stringify!($width), "}")
        };
        ($width:expr; $col:ident$([$colw:expr])?, $($rest:ident$([$restw:expr])?),+) => {
            concat!(table_fmtter!($width; $col$([$colw])?),
                    table_fmtter!($width; $($rest$([$restw])?),+))
        }
    }

    // Width must be given as a string: `"10"`
    macro_rules! table {
        ([width = $width:expr] $f:ident << $($cols:ident$([$colw:expr])?),+) => {
            // Write the column headers
            writeln!($f, table_fmtter!($width; $($cols$([$colw])?),+), $(stringify!($cols)),+)?;
            // Write the rows
            for unzip_bind!($($cols),+) in nzip!($($cols),+) {
                writeln!($f, table_fmtter!($width; $($cols$([$colw])?),+),
                         // must call `format!` for format specifiers to work
                         // in the obvious way by default
                         $(format!("{}", $cols)),+)?;
            }
        }
    }

    // NOTE: deliberately quick and dirty
    impl std::fmt::Debug for RegionInf<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let gr = &self.context.gr;

            // Put up a function header
            writeln!(f, "{:^40}", format!("== function {:?} ==", gr.id))?;

            let lts = transpose_lifetimes(&self.lifetimes, self.context);
            let constrs = transpose_constraints(&self.constraints, self.context);

            // Let's have some other columns, too, that aren't tied to the
            // statement order. I want to see what all the lifetimes in each
            // variable are.
            let (locals, types): (Vec<_>, Vec<_>) = self
                .context
                .gr
                .locals
                .idx_enumerate()
                .map(|(idx, local)| (idx, local.ty.fmt_with(self.context.ctx)))
                .unzip();
            let local = locals.iter();
            let type_ = types.iter();
            let regions = locals
                .iter()
                .map(|local| self.ascriptions.local_ascriptions(*local))
                .map(|ascrs| Seq(ascrs.collect()));

            table!([width = 10] f << local[8], type_[8], regions[16]);

            f.write_str("\n")?;

            for (blk_id, block) in gr.idx_enumerate() {
                // Write the block headline
                writeln!(f, "[[ {}: {} ]]", blk_id, block.kind)?;

                // Make the columns
                let linum = 0..;
                let stmt = block
                    .stmts
                    .iter()
                    .map(|stmt| stmt as &dyn std::fmt::Display)
                    // ...and include the block tail.
                    .chain(std::iter::once(&"term" as &dyn std::fmt::Display));
                let vars = self.liveness[blk_id].iter();
                let regions = lts[blk_id].iter();
                let constrs = constrs[blk_id].iter();
                let refs = (0..).map(|stmt| {
                    let pt = GraphPt { blk: blk_id, stmt };
                    self.ascriptions.refs.get(&pt).map_or_else(
                        || String::new(),
                        |ln| format!("{}", self.ascriptions.loans[*ln].ascr),
                    )
                });

                table!([width = 10] f <<
                       linum[6], stmt[20], vars[16], constrs[12], refs, regions[18]
                );

                f.write_str("\n")?;
            }
            f.write_str("\n")?;
            Ok(())
        }
    }

    /// Transpose lifetimes, quickly and dirtily.
    fn transpose_lifetimes(
        lifetimes: &LifetimeStore,
        context: &DataflowCtx,
    ) -> Store<BlockId, Vec<BitSet<LtId>>> {
        let num_regions = lifetimes.len();
        let mut store = Store::new();
        for block in context.gr.iter() {
            store.insert(vec![BitSet::empty(num_regions); block.len()]);
        }

        for (lt, lifetime) in lifetimes.idx_enumerate() {
            for pt in lifetime.iter() {
                store[pt].set(lt, true);
            }
        }
        store
    }

    /// Transpose constraints, quickly and dirtily
    fn transpose_constraints(
        constraints: &Constraints,
        context: &DataflowCtx,
    ) -> Store<BlockId, Vec<Seq<OutlivesP>>> {
        let mut store = Store::new();
        for block in context.gr.iter() {
            store.insert(vec![Seq(vec![]); block.len()]);
        }

        for constr in constraints.iter() {
            let GraphPt { blk, stmt } = constr.pt;
            store[blk][stmt].0.push(constr.prop.clone());
        }

        store
    }

    /// A vec wrapper that displays with only spaces for delimiters
    #[derive(Clone)]
    struct Seq<T>(Vec<T>);

    impl<T: fmt::Display> fmt::Display for Seq<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut elems = self.0.iter();
            if let Some(head) = elems.next() {
                write!(f, "{}", head)?;
                for elem in elems {
                    write!(f, " {}", elem)?;
                }
            }
            Ok(())
        }
    }
}
