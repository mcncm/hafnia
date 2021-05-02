//! The analysis in this file checks for things that occur under a linear
//! conditional. For example, it's not clear what--if any--sensible
//! interpretation can be given to a measurement under a linear condition. It's
//! also quite unclear what the meaning of clasical control flow is under a
//! linear condition.
//!
//! This one is a little bit complicated, and the checking stage necessarily
//! interprocedural: you have to ensure that no delinearization occurs anywhere
//! in the call graph downstream of a location within a linear conditional.

use super::common::{Backward, DataflowAnalysis, Lattice, SummaryAnalysis};
use crate::{
    ast::{FnId, UnOpKind},
    cavy_errors::ErrorBuf,
    mir::{self, BlockId, BlockKind, GraphLoc, RvalueKind},
    source::Span,
    store::Store,
};
use std::collections::{
    hash_map::{Entry, OccupiedEntry},
    HashMap, HashSet,
};

/// A measurement that has taken place under a linear condition
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MeasUnderCond {
    /// The block terminated by the enclosing linear condition
    pub cond: BlockId,
    /// the span at which the delinearization took place
    pub span: Span,
}

/// The state for this summary analysis is the collection of measurement
/// operators and callsites that have appeared under a linear conditional.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SubCondData {
    /// Does this procedure feature any delinearization operators,
    /// subconditional or otherwise? We'll use this data when we're traversing
    /// the call graph to identify interprocedurally subconditional
    /// delinearizations.
    pub has_delin: bool,
    /// Whether the routine has any classical control at all
    pub has_cc: bool,
    /// Sites of subconditional delinearization operators.
    pub delins: HashSet<MeasUnderCond>,
    /// Function call sites under a linear condition.
    /// NOTE could be a `Vec`?
    pub sublin_calls: HashSet<(FnId, Span)>,
}

pub struct SubCondAnalysis<'a> {
    sub_cond_data: &'a mut Store<FnId, SubCondData>,
    controls: &'a (),
    state: SubCondData,
}

impl<'a> SubCondAnalysis<'a> {
    pub fn new(sub_cond_data: &'a mut Store<FnId, SubCondData>, controls: &'a ()) -> Self {
        Self {
            sub_cond_data,
            controls,
            state: SubCondData::default(),
        }
    }
}

impl<'a> SummaryAnalysis for SubCondAnalysis<'a> {
    /// If we encounter a delinearization operator, add that.
    fn trans_stmt(&mut self, _stmt: &mir::Stmt, _loc: &GraphLoc) {
        // let (_place, rhs) = match &stmt.kind {
        //     mir::StmtKind::Assn(place, rhs) => (place.clone(), rhs),
        //     _ => return,
        // };

        // if let RvalueKind::UnOp(UnOpKind::Delin, _) = rhs.data {
        //     self.state.has_delin = true;
        //     if let Some(blk) = data.sup_lin_branch {
        //         self.state.delins.insert(MeasUnderCond {
        //             cond: blk,
        //             span: rhs.span,
        //         });
        //     }
        // }
    }

    fn trans_block(&mut self, _block: &BlockKind, _loc: &BlockId) {
        // if let (BlockKind::Call { callee, span, .. }, Some(_)) = (block, data.sup_lin_branch) {
        //     state.sublin_calls.insert((*callee, *span));
        // }
    }
}

/// Run checks on the subconditional behavior of the program: is there
/// measurement--including interprocedurally--under a linear conditional? Is
/// there classical control under a linear conditional?
pub fn check(
    errs: &mut ErrorBuf,
    // The data collected from each function in the subconditional analysis
    data: &Store<FnId, SubCondData>,
    // The global call graph
    gr: &Store<FnId, super::call_graph::CallSites>,
) {
    let checker = SubCondChecker::new(data, gr);
    checker.check(errs);
}

/// A terribly named type that I should/will rename. Analyzed properties of
/// functions in relation to their position in the call graph.
#[derive(Default, Debug)]
struct FuncProps {
    /// Is this function upstream (inclusively) of a delinearization operator in
    /// the call graph?
    over_delin: bool,
    /// Is this function upstream (inclusively) of classical control in the call
    /// graph?
    over_cc: bool,
}

/// Private struct that maintains state for checking the subconditional analysis
struct SubCondChecker<'a> {
    /// Subconditional-related properties of functions in the call graph
    func_props: HashMap<FnId, FuncProps>,
    data: &'a Store<FnId, SubCondData>,
    gr: &'a Store<FnId, super::call_graph::CallSites>,
}

impl<'a> SubCondChecker<'a> {
    fn new(
        data: &'a Store<FnId, SubCondData>,
        gr: &'a Store<FnId, super::call_graph::CallSites>,
    ) -> Self {
        Self {
            func_props: HashMap::new(),
            data,
            gr,
        }
    }

    fn check(mut self, errs: &mut ErrorBuf) {
        for (_func, data) in self.data.idx_enumerate() {
            // Check within function
            for delin in &data.delins {
                // TODO report the location of the condition
                let span = delin.span;
                errs.push(errors::MeasUnderLinCond { span });
            }
            // Now check in function calls
            for (call_func, call_span) in &data.sublin_calls {
                let props = self.props(*call_func);
                if props.over_delin {
                    errs.push(errors::UpstreamOfDelin { delin: *call_span });
                }

                if props.over_cc {
                    // TODO
                }
            }
        }
    }

    /// Gets the properties of a single function. Mutually recursive with `compute_props`.
    fn props(&mut self, func: FnId) -> &FuncProps {
        #![allow(clippy::map_entry)]
        // FIXME this does *three* hash table lookups, but in principle only
        // requires one. How can I use the `Entry` API to solve this and still
        // satisfy the borrow checker?
        if !self.func_props.contains_key(&func) {
            let props = self.compute_props(func);
            self.func_props.insert(func, props);
        }

        self.func_props.get(&func).unwrap()
    }

    fn compute_props(&mut self, func: FnId) -> FuncProps {
        // functions called by a given function
        let callees = &self.gr[func];
        // First the effects of the function itself
        let func_data = &self.data[func];
        let props = FuncProps {
            over_delin: func_data.has_delin,
            over_cc: func_data.has_cc,
        };
        // Then apply the effects of all the subroutines
        callees.iter().fold(props, |acc, (callee, _)| {
            let other = self.props(*callee);
            FuncProps {
                over_delin: acc.over_delin | other.over_delin,
                over_cc: acc.over_cc | other.over_cc,
            }
        })
    }
}

mod errors {
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[msg = "quantum control upstream of measurement"]
    pub struct UpstreamOfDelin {
        #[span]
        /// The location of the measurement
        pub delin: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "measurement under quantum control"]
    pub struct MeasUnderLinCond {
        #[span]
        /// The location of the measurement
        pub span: Span,
    }
}
