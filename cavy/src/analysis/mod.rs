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
mod common;
mod feedback;
mod linearity;

use crate::{ast::FnId, cavy_errors::ErrorBuf, context::Context, mir::Mir, store::Store};

use self::common::{Analysis, DataflowRunner, SummaryRunner};

pub fn check(mir: &Mir, ctx: &Context) -> Result<(), ErrorBuf> {
    let mut errs = ErrorBuf::new();

    // Maybe I should consider making analyses operate on the whole MIR so as
    // not to pollute the top level like this
    let mut call_sites: Store<FnId, call_graph::CallSites> = Store::new();

    for (fn_id, gr) in mir.graphs.idx_enumerate() {
        let linearity_res = linearity::LinearityAnalysis {}.into_runner(ctx, gr).run();
        for (local, &snd_move) in linearity_res.exit_state.double_moved.iter() {
            let fst_move = linearity_res.exit_state.moved[local];
            errs.push(errors::DoubleMove {
                span: fst_move,
                snd_move,
            });
        }

        if !ctx.conf.arch.feedback {
            let feedback_res = feedback::FeedbackAnalysis {}.into_runner(ctx, gr).run();
            for (local, snd_span) in feedback_res.exit_state.lin.into_iter() {
                if let Some(_fst_span) = feedback_res.exit_state.delin.get(&local) {
                    errs.push(errors::ClassicalFeedback { span: snd_span });
                }
            }
        }

        // Awkward; figure out equivlent of `into_runner` for summary analyses
        let calls = SummaryRunner::new(call_graph::CallGraphAnalysis {}, gr, ctx).run();
        let idx = call_sites.insert(calls);
        // Make sure that there is no accidental reordering. This caught a bug
        // before! Consider moving into a test.
        debug_assert!(idx == fn_id);
    }

    if !ctx.conf.arch.recursion {
        call_graph::check_recursion(&mut errs, &call_sites);
    }

    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

mod errors {
    use crate::cavy_errors::Diagnostic;
    use crate::context::SymbolId;
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    pub struct DoubleMove {
        #[msg = "linear variable moved twice"]
        /// The first use site
        pub span: Span,
        #[help = "used again here"]
        /// The second use site
        pub snd_move: Span,
    }

    #[derive(Diagnostic)]
    pub struct ClassicalFeedback {
        #[msg = "detected classical feedback"]
        /// The second use site
        pub span: Span,
    }
}
