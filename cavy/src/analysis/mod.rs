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

pub mod common;
pub mod feedback;
pub mod linearity;

use crate::{cavy_errors::ErrorBuf, context::Context, mir::Mir};

use self::common::{Analysis, DataflowRunner};

pub fn check(mir: &Mir, ctx: &Context) -> Result<(), ErrorBuf> {
    let mut errs = ErrorBuf::new();
    for (_, gr) in mir.graphs.iter() {
        let linearity_res = linearity::LinearityAnalysis {}.into_runner(ctx, gr).run();
        // Really expensive, lots of extra work. Maybe we should have a unique
        // `End` block, and just have to check at that one block whether
        // anything has ever been moved twice.
        for &snd_span in linearity_res.exit_state.double_moved.values() {
            errs.push(errors::DoubleMove { span: snd_span });
        }

        if !ctx.conf.arch.feedback {
            let feedback_res = feedback::FeedbackAnalysis {}.into_runner(ctx, gr).run();
            for (local, snd_span) in feedback_res.exit_state.lin.into_iter() {
                if let Some(_fst_span) = feedback_res.exit_state.delin.get(&local) {
                    errs.push(errors::ClassicalFeedback { span: snd_span });
                }
            }
        }
    }

    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

mod errors {
    use crate::cavy_errors::Diagnostic;
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    pub struct DoubleMove {
        #[msg = "linear variable moved twice"]
        /// The second use site
        pub span: Span,
    }

    #[derive(Diagnostic)]
    pub struct ClassicalFeedback {
        #[msg = "detected classical feedback"]
        /// The second use site
        pub span: Span,
    }
}
