//! The analysis in this file checks for correct use of `unsafe` operations
//! (currently only the `assert` statement and calling an `unsafe` function).

use crate::{
    ast::FnId,
    cavy_errors::{Diagnostic, ErrorBuf},
    mir::{self, BlockId, BlockKind, FnCall, GraphData, GraphLoc},
    source::Span,
    store::Store,
};

use super::common::SummaryAnalysis;

/// The possible origins of unsafety
enum UnsafetyKind {
    /// Used an assert
    Assert,
    /// Called an unsafe function
    UnsafeCall(FnId),
}

struct UnsafeOperation {
    kind: UnsafetyKind,
    span: Span,
}

pub struct UnsafeAnalysis<'a> {
    /// Is this function marked `unsafe`? If so, disable the analysis.
    is_unsafe: bool,
    /// Satellite data of all the graphs; need this to check call safety
    graph_data: &'a Store<FnId, GraphData>,
    /// Incorrect uses of unsafe discovered
    violations: Vec<UnsafeOperation>,
}

impl<'a> UnsafeAnalysis<'a> {
    pub fn new(graph_data: &'a Store<FnId, GraphData>, fn_id: FnId) -> Self {
        let is_unsafe = graph_data[fn_id].is_unsafe;
        Self {
            is_unsafe,
            graph_data,
            violations: Vec::new(),
        }
    }

    /// Is a call in an invalid position?
    fn unsafe_call(&self, call: &FnCall) -> bool {
        let fn_unsafe = self.graph_data[call.callee].is_unsafe;
        fn_unsafe && !call.scope_data.in_unsafe
    }

    fn to_err(&self, violation: &UnsafeOperation) -> Box<dyn Diagnostic> {
        let span = violation.span;
        match violation.kind {
            UnsafetyKind::Assert => Box::new(errors::SafetyViolation {
                span,
                msg: "asserted expression",
            }),
            UnsafetyKind::UnsafeCall(fn_id) => {
                let name = self.graph_data[fn_id].def_name;
                Box::new(errors::UnsafeCall { span, func: name })
            }
        }
    }
}

impl<'a> SummaryAnalysis for UnsafeAnalysis<'a> {
    fn trans_stmt(&mut self, stmt: &mir::Stmt, _loc: &GraphLoc) {
        match stmt.kind {
            mir::StmtKind::Assert(_) => {
                if !stmt.scope_data.in_unsafe {
                    self.violations.push(UnsafeOperation {
                        kind: UnsafetyKind::Assert,
                        span: stmt.span,
                    })
                }
            }
            _ => {}
        }
    }

    fn trans_block(&mut self, block: &BlockKind, _loc: &BlockId) {
        if let BlockKind::Call(call) = block {
            if self.unsafe_call(&call) {
                self.violations.push(UnsafeOperation {
                    kind: UnsafetyKind::UnsafeCall(call.callee),
                    span: call.span,
                })
            }
        }
    }

    fn check(&self, errs: &mut ErrorBuf) {
        for err in &self.violations {
            errs.0.push(self.to_err(err));
        }
    }

    fn enabled(&self) -> bool {
        !self.is_unsafe
    }
}

/// Run checks on the unsafe behavior of the program.
pub fn check(_errs: &mut ErrorBuf) {
    todo!();
}

mod errors {
    use crate::{context::SymbolId, source::Span};
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[msg = "{msg} outside `unsafe` block"]
    pub struct SafetyViolation {
        #[span]
        /// The location of the unsafety
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[msg = "called unsafe function `{func}` outside `unsafe` block"]
    pub struct UnsafeCall {
        #[span]
        /// The location of the unsafety
        pub span: Span,
        #[ctx]
        pub func: SymbolId,
    }
}
