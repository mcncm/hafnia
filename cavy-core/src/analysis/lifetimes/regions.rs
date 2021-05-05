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
        for (_pt, _stmt) in enumerate_stmts(self.context.gr) {}
    }

    // For the liveness constraints, we'll just work at the variable granularity
    // for now.
    fn live_vars_at(&self, _pt: GraphPt) -> u32 {
        todo!();
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
