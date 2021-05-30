//! This tiny crate just contains a macro for (Rust-)compile-time compilation of
//! Cavy code. It has to live in its own, separate crate, because Rust requires
//! crates to form a DAG. If this macro were included in the `cavy-macros`
//! crate, it would force a cyclic dependency between that crate and the cavy
//! library crate.

#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_span)]

use std::fmt;

use cavy_core::{cavy_errors, compile, context::Context, default_context, source, util::FmtWith};
use proc_macro::{Delimiter, Group, LineColumn, TokenStream, TokenTree};
use quote::quote;
use syn;

mod types;

/// Compile Cavy code at Rust-compile-time. This is the best and easiest way to
/// use Cavy as an embedded domain-specific language for quantum coprocessors
/// within Rust.
///
/// Currently, this macro has some limitations:
///
/// * It offers no means of giving non-default compiler options.
///
/// * It requires the user to depend on `serde_json`, and to bring lots of cavy
///   types into scope.
///
/// * There is no "lazy-loading" of the circuit; it will be deserialized and
///   built on every loop iteration.
#[proc_macro]
pub fn inline_cavy(input: TokenStream) -> TokenStream {
    default_context!(ctx);
    let src = stringify_src(input);
    let id = ctx.srcs.insert_input(&src.0);
    let circ = compile::compile_circuit(id, &mut ctx);
    // Can only get Ok(None) if compiler options ask to stop early
    let circ = circ.map(|circ| circ.unwrap());

    match circ {
        Ok(circ) => {
            let circ = serde_json::to_string(&circ).unwrap();

            (quote! { {
                let circ: cavy::circuit::CircuitBuf = serde_json::from_str(#circ).unwrap();
                circ
            } })
            .into()
        }
        Err(errs) => {
            let spans = src.1;
            emit_diagnostics(errs, spans, &mut ctx);
            // Have to return *something*
            (quote! { cavy::circuit::CircuitBuf::new() }).into()
        }
    }
}

fn emit_diagnostics(errs: cavy_errors::ErrorBuf, spans: Vec<proc_macro::Span>, ctx: &mut Context) {
    for err in errs.0.into_iter() {
        emit_diagnostic(err, &spans, ctx);
    }
}

/// A struct to carry a "private" `impl` for `cavy_errors::Diagnostic`
struct MsgHelper<'a> {
    diagnostic: &'a dyn cavy_errors::Diagnostic,
}

impl<'a> From<&'a dyn cavy_errors::Diagnostic> for MsgHelper<'a> {
    fn from(d: &'a dyn cavy_errors::Diagnostic) -> Self {
        Self { diagnostic: d }
    }
}

impl<'c, 'a> FmtWith<Context<'c>> for MsgHelper<'a> {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.diagnostic.message(ctx, f)
    }
}

fn emit_diagnostic(
    err: Box<dyn cavy_errors::Diagnostic>,
    rspans: &[proc_macro::Span],
    ctx: &mut Context,
) {
    let level = translate_level(err.level());
    let msg = format!("[cavy] {}", MsgHelper::from(&*err).fmt_with(ctx));
    let spans: Vec<proc_macro::Span> = err
        .spans()
        .into_iter()
        .map(|report| translate_span(report.span, &rspans, ctx))
        .collect();
    let diag = proc_macro::Diagnostic::spanned(spans, level, msg);
    diag.emit();
}

/// Translate the internal Cavy diagnostic level to the proc macro `Level` api.
fn translate_level(level: &cavy_errors::DiagnosticLevel) -> proc_macro::Level {
    match level {
        cavy_errors::DiagnosticLevel::Error => proc_macro::Level::Error,
        cavy_errors::DiagnosticLevel::Warn => proc_macro::Level::Warning,
    }
}

/// This ridicuous function is necessary because we can't actually construct a
/// `proc_macro::Span` with arbitrary line and column numbers.
fn translate_span(
    cspan: source::Span,
    rspans: &[proc_macro::Span],
    ctx: &Context,
) -> proc_macro::Span {
    let origin = &ctx.srcs[cspan.src_id];
    // Get the beginning and ending `LineColumn`s
    let start = lincol(cspan.start, origin);
    let end = lincol(cspan.end, origin);

    // Now get the first and last rustc `Span`s covered
    let start = span_from(&start, rspans);
    let end = span_from(&end, rspans);

    // Then return the smallest connected span containing them
    start.join(end).unwrap()
}

fn lincol(pos: usize, origin: &source::SrcObject) -> LineColumn {
    let line = origin.get_line(pos);
    let column = pos - line.start;
    // Adjustment for a slight impedance mismatch between my conventions and
    // `rustc`'s: for me, line numbers start at 1. For `rustc`, they start at 0.
    let line = line.linum.get() - 1;
    LineColumn { line, column }
}

/// Get the span containing a `LineColumn`
fn span_from(lc: &LineColumn, rspans: &[proc_macro::Span]) -> proc_macro::Span {
    let idx = rspans.binary_search_by_key(lc, |rspan| rspan.start());
    let idx = idx.unwrap(); // why not
    rspans[idx]
}

/// The details here were sorted out with the help of Mara Bos' [blog
/// post](https://blog.m-ou.se/writing-python-inside-rust-1/) on whitespace
/// reconstruction for the `inline-python` crate. This implementation is
/// fundamentally the same, written in a (slightly) different style. Thank you,
/// Mara!
fn stringify_src(input: TokenStream) -> (String, Vec<proc_macro::Span>) {
    let mut s = Source::default();
    s.consume(input);
    (s.source, s.spans)
}

#[derive(Default)]
struct Source {
    source: String,
    /// We have to carry around all the `Span`s from the source because we can't
    /// actually _construct_ a `proc_macro::Span`.
    spans: Vec<proc_macro::Span>,
    line: usize,
    col: usize,
}

impl Source {
    fn consume(&mut self, input: TokenStream) {
        for token in input {
            if let TokenTree::Group(group) = token {
                self.finish_group(group);
            } else {
                self.advance_to(&token.to_string(), token.span());
            }
        }
    }

    fn finish_group(&mut self, group: Group) {
        let delims = match group.delimiter() {
            Delimiter::Parenthesis => ("(", ")"),
            Delimiter::Brace => ("{", "}"),
            Delimiter::Bracket => ("[", "]"),
            _ => panic!(),
        };

        let open_span = group.span_open();
        self.spans.push(open_span);

        self.advance_to(delims.0, group.span_open());
        self.consume(group.stream());
        self.advance_to(delims.1, group.span_close());
    }

    fn advance_to(&mut self, s: &str, span: proc_macro::Span) {
        self.spans.push(span);
        let loc = span.start();

        let line_diff = loc.line - self.line;
        self.line = loc.line;
        self.source.extend(std::iter::repeat('\n').take(line_diff));
        if line_diff != 0 {
            self.col = 0;
        }

        /*
        `saturating_sub`: rustc has some odd ideas about how tokens are formed.
        Multi-character operators are actually _multiple_ tokens in `rustc`, one
        for each character, but which share a common (multi-character) span. It
        turns out that, when encountering the second token in such an operator,
        `self.col` will have advanced _past_ the start of that token; that is,
        `loc.column`.

        This is fine as long as we *do nothing* in such a case, adding no
        whitespace to the source. But this will happen as long as `col_diff ==
        0`.
        */
        let col_diff = loc.column.saturating_sub(self.col);
        self.col = loc.column;
        self.source.extend(std::iter::repeat(' ').take(col_diff));

        // Add the new string
        self.source += s;
        self.col += s.len();
    }
}

/// Builds a Cavy type from a Rust type
#[proc_macro_derive(Cavy, attributes(msg, span, ctx))]
pub fn cavy_type(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    types::impl_cavy_error_macro(input)
}
