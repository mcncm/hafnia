use std::fmt;

use crate::{mir::*, store::Store, util::FmtWith};

use super::{
    super::{DataflowCtx, DataflowRunner},
    ascription::{self, Ascriptions},
    liveness::{self, LiveVars},
    ltdbg,
    util::enumerate_stmts,
    LifetimeStore, LtId,
};

pub fn infer_regions(context: &DataflowCtx) -> LifetimeStore {
    let mut lifetimes = LifetimeStore::new();
    let ascriptions = ascription::ascribe(&mut lifetimes, &context);

    let liveness_ana = liveness::LivenessAnalysis::new(context.gr);
    let liveness = DataflowRunner::new(liveness_ana, &context)
        .run()
        .stmt_states;

    ltdbg!(liveness, context);

    let mut reginf = RegionInf {
        lifetimes: &mut lifetimes,
        ascriptions,
        liveness,
        context,
        constraints: Constraints::new(),
    };

    reginf.collect_liveness_constraints();

    println!("{:?}", reginf);

    // for lt in reginf.lifetimes.iter() {
    //     println!("{:?}", lt);
    // }

    reginf.collect_subtyping_constraints();
    reginf.collect_reborrow_constraints();

    lifetimes
}

/// This struct does region inference to compute lifetimes.
struct RegionInf<'a> {
    lifetimes: &'a mut LifetimeStore,
    ascriptions: Ascriptions<'a>,
    liveness: Store<BlockId, Vec<LiveVars>>,
    context: &'a DataflowCtx<'a>,
    constraints: Vec<Outlives>,
}

type Constraints = Vec<Outlives>;

/// The lifetime subtype constraint representation described in `#Lifetime
/// inference constraints` of the NLL RFC.
struct Outlives {
    long: LtId,
    shrt: LtId,
    pt: GraphPt,
}

/// A liveness constraint. This struct isn't *used* for much--it's entered
/// straight into the lifetime set--but it is useful to keep around for its
/// `Debug` implementation.
struct LiveAt {
    lt: LtId,
    pt: GraphPt,
}

impl<'a> RegionInf<'a> {
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
                for lt in self.ascriptions.local_ascriptions(var) {
                    self.lifetimes[lt].insert(pt);
                }
            }
        }
    }

    fn insert_liveness_constraint(&mut self, constr: LiveAt) {
        self.lifetimes[constr.lt].insert(constr.pt);
    }

    /// See [Subtyping](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#subtyping)
    fn collect_subtyping_constraints(&mut self) {}

    /// See [Reborrow
    /// Constriants](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#reborrow-constraints)
    fn collect_reborrow_constraints(&mut self) {}
}

// === formatting impls ===

impl fmt::Debug for Outlives {
    /// Exact format from NLL RFC: `('foo: 'p) @ A/1`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}: {}) @ {:?}", self.long, self.shrt, self.pt)
    }
}

impl fmt::Debug for LiveAt {
    // Exactly as in the NLL RFC: `('p: {A/1}) @ A/1`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}: {{{:?}}}) @ {:?}", self.lt, self.pt, self.pt)
    }
}

impl FmtWith<LifetimeStore> for LtId {
    fn fmt(&self, store: &LifetimeStore, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lifetime = &store[*self];
        for pt in lifetime.pts.iter() {
            let constr = LiveAt { lt: *self, pt: *pt };
            writeln!(f, "{:?}", constr)?;
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
        ($width:expr; $col:expr) => {
            concat!("{:", stringify!($width), "}")
        };
        ($width:expr; $col:expr, $($rest:expr),+) => {
            concat!(table_fmtter!($width; $col), table_fmtter!($width; $($rest),+))
        }
    }

    // Width must be given as a string: `"10"`
    macro_rules! table {
        ([width = $width:expr] $f:ident << $($cols:ident),+) => {
            writeln!($f, table_fmtter!($width; $($cols),+), $(stringify!($cols)),+)?;
            for unzip_bind!($($cols),+) in nzip!($($cols),+) {
                writeln!($f, table_fmtter!($width; $($cols),+), $(format!("{}", $cols)),+)?;
            }
        }
    }

    impl std::fmt::Debug for RegionInf<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            for (blk_id, block) in self.context.gr.idx_enumerate() {
                let lts = transpose_lifetimes(self.lifetimes, self.context);

                // Write the block headline
                let block = &self.context.gr[blk_id];
                writeln!(f, "== {} :: {} ==", blk_id, block.kind)?;

                // Make the columns
                let vars = self.liveness[blk_id].iter();
                let regions = lts[blk_id].iter();
                let stmts = block.stmts.iter();

                table!( [width = 10] f << vars, regions, stmts );

                f.write_str("\n")?;
            }
            Ok(())
        }
    }

    /// Transpose lifetimes, quickly and dirtily.
    pub fn transpose_lifetimes(
        lifetimes: &LifetimeStore,
        context: &DataflowCtx,
    ) -> Store<BlockId, Vec<BitSet<LtId>>> {
        let num_regions = lifetimes.len();
        let mut store = Store::new();
        for block in context.gr.iter() {
            store.insert(vec![BitSet::empty(num_regions); block.stmts.len()]);
        }

        for (lt, lifetime) in lifetimes.idx_enumerate() {
            for pt in lifetime.iter() {
                store[pt].set(lt, true);
            }
        }
        store
    }
}
