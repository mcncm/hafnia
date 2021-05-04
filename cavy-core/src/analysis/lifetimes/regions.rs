use std::fmt;

use crate::{mir::*, store::Store};

use super::{
    super::{DataflowCtx, DataflowRunner},
    ascription::{self, Ascriptions},
    liveness::{self, LiveVars},
    ltdbg, LifetimeStore, LtId,
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
    loc: GraphLoc,
}

impl<'a> RegionInf<'a> {
    /// The liveness constraints are never collected into `Self::constraints`;
    /// they're just entered directly into each lifetime.
    ///
    /// See [Liveness](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#liveness)
    fn collect_liveness_constraints(&mut self) {
        todo!()
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
        write!(f, "({}: {}) @ {:?}", self.long, self.shrt, self.loc)
    }
}

impl fmt::Display for LtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", self.0)
    }
}
