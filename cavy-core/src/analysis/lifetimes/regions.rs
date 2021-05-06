use std::fmt;

use crate::{mir::*, store::Store, types::RefKind, util::FmtWith};

use super::{
    super::{graph, DataflowCtx, DataflowRunner},
    ascription::{self, AscrNode, AscriptionStore, LtAscr},
    liveness::{self, LiveVars},
    util::enumerate_stmts,
    Lifetime, LifetimeStore, LtId,
};

pub fn infer_regions(context: &DataflowCtx) -> LifetimeStore {
    let mut lifetimes = LifetimeStore::new();
    let ascriptions = ascription::ascribe(&mut lifetimes, &context);

    let liveness_ana = liveness::LivenessAnalysis::new(context.gr);
    let liveness = DataflowRunner::new(liveness_ana, &context)
        .run()
        .stmt_states;

    let mut reginf = RegionInf {
        lifetimes: &mut lifetimes,
        ascriptions,
        liveness,
        context,
        constraints: Constraints::new(),
    };

    reginf.collect_constraints();
    reginf.solve_constraints();

    println!("{:?}", reginf);
    for constr in reginf.constraints.constrs {
        println!("{}", constr);
    }

    lifetimes
}

/// This struct does region inference to compute lifetimes.
struct RegionInf<'a> {
    lifetimes: &'a mut LifetimeStore,
    ascriptions: AscriptionStore<'a>,
    liveness: Store<BlockId, Vec<LiveVars>>,
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
        for (pt, _stmt) in enumerate_stmts(self.context.gr) {
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
        for (pt, stmt) in enumerate_stmts(self.context.gr) {
            // StmtKind::Assn(lhs, Rvalue::) => {}
            let (lhs, rvalue) = match &stmt.kind {
                StmtKind::Assn(lhs, Rvalue { data: rvalue, .. }) => (lhs, rvalue),
                // only assignments should generate subtyping constraints
                _ => return,
            };

            match rvalue {
                RvalueKind::BinOp(_, lop, rop) => {
                    self.sub_constr_oper(pt, lhs, lop);
                    self.sub_constr_oper(pt, lhs, rop);
                }
                RvalueKind::UnOp(_, op) | RvalueKind::Use(op) => {
                    self.sub_constr_oper(pt, lhs, op);
                }
                RvalueKind::Ref(refr, place) => {
                    self.sub_constr_refr(*refr, pt, lhs, place);
                }
            };
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
                // Recursively apply the subtyping rule, with `rtree <: ltree`
                self.constraints.insert_sub_constr(pt, rtree, ltree);
            }
            (None, None) => {}
            _ => unreachable!("inconsistent ascriptions"),
        }
    }

    /// Insert a constraint from a borrow statement. This method is analogous to
    /// `Self::sub_constr`, except that the sides are "unbalanced", so we have
    /// to manually insert one level of constraint before entering the
    /// `Constraints::insert_sub_constr_{..}` recursive pair.
    fn sub_constr_refr(&mut self, refr: RefKind, pt: GraphPt, lhs: &Place, rhs: &Place) {
        let ltree = self.ascriptions.locals[lhs.root]
            .as_ref()
            .expect("lhs of borrow must have a lifetime");
        let long = ltree
            .this
            .as_ref()
            .expect("lhs must have a root-level ascription");
        let shrt = &self.ascriptions.refs[&pt];
        debug_assert!(long.kind == refr && shrt.kind == refr);

        // insert the constraint at the unbalanced level
        self.constraints.outlives_at(long.lt, shrt.lt, pt);

        // finally, recurse on any contained types
        debug_assert_eq!(ltree.slots.len(), 1);
        match (
            ltree.slots[0].as_ref(),
            self.ascriptions.locals[rhs.root].as_ref(),
        ) {
            (Some(ltree), Some(rtree)) => {
                self.constraints
                    .insert_sub_constr_inner(Some(refr), pt, rtree, ltree);
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
                if shrt == long {
                    dbg!("got the same lifetime twice");
                    return false;
                }

                // Safety: if the two lifetimes are identical, we have already returned.
                let (long, shrt) = unsafe { lifetimes.get_two_unchecked_mut(long, shrt) };

                long.extend_to(shrt, constr.pt, gr)
            })
            .any(|x| x)
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
            let mask = other.leading_ones();

            let ones = this.count_ones();
            // Add the other lifetime's points
            this[..mask].set_all(true);
            // Mark whether we got new points
            changed |= ones != this.count_ones();

            // End when we go out of the other lifetime
            if other.first_zero().is_some() {
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
                Some(LtAscr {
                    kind: shrt_kind,
                    lt: shrt_lt,
                }),
                Some(LtAscr {
                    kind: long_kind,
                    lt: long_lt,
                }),
                // NOTE: it is *not* the case that `&mut T <: &T`. The former is
                // *coercible* to the latter, but it is not a subtype; if it
                // were, you could break all the rules.
            ) if shrt_kind == long_kind => {
                // insert the constraints at this level
                self.outlives_at(*long_lt, *shrt_lt, pt);

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

    fn outlives_at(&mut self, long: LtId, shrt: LtId, pt: GraphPt) {
        self.constrs.push(LocalP {
            prop: OutlivesP { long, shrt },
            pt,
        });
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

    impl std::fmt::Debug for RegionInf<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let lts = transpose_lifetimes(self.lifetimes, self.context);
            let constrs = transpose_constraints(&self.constraints, self.context);
            for (blk_id, block) in self.context.gr.idx_enumerate() {
                // Write the block headline
                writeln!(f, "== {} ==", blk_id)?;

                // Make the columns
                let linum = 0..;
                let stmt = block
                    .stmts
                    .iter()
                    .map(|stmt| stmt as &dyn std::fmt::Display)
                    // ...and include the block tail.
                    .chain(std::iter::once(&block.kind as &dyn std::fmt::Display));
                let vars = self.liveness[blk_id].iter();
                let regions = lts[blk_id].iter();
                let constrs = constrs[blk_id].iter();

                table!( [width = 10] f << linum[6], stmt[16], vars, regions, constrs );

                f.write_str("\n")?;
            }
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
