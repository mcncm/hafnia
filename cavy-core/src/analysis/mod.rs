//! This module contains the types and traits used for dataflow analyses. Here
//! are some of the analyses we would like to perform:
//! + linear (affine) values are used (at most) once
//! - linear values aren't used while "borrowed" (although this is still
//!   a hazy and ill-defined concept)
//! - ordered values are used in order
//! - switch blocks consume the same linear (affine) values in each arm
//! - checking for classical feedback
//!
//! As in a few other modules in this project, the architecture is roughly like
//! that of rustc's. The `Analysis` trait is completely analogous to
//! `rustc_mir::dataflow::Analysis`, and `AnalysisRunner` to
//! `rustc_mir::dataflow::Engine`.
//!
//! NOTE There are several improvements that could be made to this module.
//!
//! * One would be to walk each graph only once, notifying *every* registered
//!   analysis at each step. It's not quite that simple, of course, because you
//!   can only do a single traversal if the graph is acyclic. In the case where
//!   you must iterate to find a fixed point, this picture gets a little more
//!   complicated.
//!   
//! * Another improvement would be to parallellize all non-interprocedural
//!   analyses. But without profiling (or even running into performance issues),
//!   this would be a foolish optimization.
//!
//! * Analysis states could be represented with persistent data structures,
//!   rather than copying them on each block. Again, this could become much more
//!   difficult if iteration is necessary.

mod call_graph;
pub mod controls;
mod dataflow;
// mod conditional;
pub mod borrows;
mod feedback;
mod fmt;
pub mod graph;
mod linearity;
mod subconditional;
mod unsafety;

use std::collections::BTreeMap;

use crate::{
    ast::FnId,
    cavy_errors::ErrorBuf,
    context::Context,
    mir::{Graph, GraphPt, LocalId, Mir},
    store::Store,
};

pub use self::dataflow::{
    Backward, Blockwise, DataflowAnalysis, DataflowCtx, DataflowRunner, Forward, Lattice,
    Statementwise,
};

pub use graph::dominators;

pub use dataflow::{SummaryAnalysis, SummaryRunner};

pub fn check(mir: &Mir, ctx: &Context) -> Result<(), ErrorBuf> {
    let mut errs = ErrorBuf::new();

    // Maybe I should consider making analyses operate on the whole MIR so as
    // not to pollute the top level like this
    let mut call_sites: Store<FnId, call_graph::CallSites> = Store::new();
    let mut sub_cond_data: Store<FnId, subconditional::SubCondData> = Store::new();

    for (fn_id, gr) in mir.graphs.idx_enumerate() {
        // == Dataflow analyses ==

        let context = DataflowCtx::new(gr, ctx);

        linearity::check_linearity(&context, &mut errs);

        if !ctx.conf.arch.feedback {
            let feedback_res = DataflowRunner::new(feedback::FeedbackAnalysis {}, &context)
                .run()
                // ibid
                .block_states[gr.exit_block]
                .clone();
            for (local, lin_site) in feedback_res.lin.into_iter() {
                if let Some(&delin_site) = feedback_res.delin.get(&local) {
                    errs.push(errors::ClassicalFeedback {
                        delin_site,
                        lin_site,
                    });
                }
            }
        }

        let dom = graph::DominatorAnalysis::<Forward>::new(gr);
        let _dominators = DataflowRunner::new(dom, &context).run().block_states;

        let postdom = graph::DominatorAnalysis::<Backward>::new(gr);
        let postdominators = DataflowRunner::new(postdom, &context).run().block_states;

        let controls = controls::control_places(gr, &postdominators);

        borrows::check(context, &controls, &mut errs);

        // == Summary analyses ==

        let mut call_graph_ana = call_graph::CallGraphAnalysis::new(&mut call_sites);
        let mut subcond_ana = subconditional::SubCondAnalysis::new(&mut sub_cond_data, &());
        let mut unsafe_ana = unsafety::UnsafeAnalysis::new(&mir.graph_data, fn_id);
        SummaryRunner::new(gr, ctx, Some(&mut errs))
            .register(&mut call_graph_ana)
            .register(&mut subcond_ana)
            .register(&mut unsafe_ana)
            .run();
    }

    if !ctx.conf.arch.recursion {
        call_graph::check_recursion(&mut errs, &call_sites);
    }

    subconditional::check(&mut errs, &sub_cond_data, &call_sites);

    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

mod errors {
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    // FIXME: put me in feedback module
    #[derive(Diagnostic)]
    #[msg = "detected classical feedback"]
    pub struct ClassicalFeedback {
        /// The the delinearization site
        #[span(msg = "this data was measured here...")]
        pub delin_site: Span,
        /// The linearization site
        #[span(msg = "...and later linearized")]
        pub lin_site: Span,
    }
}
