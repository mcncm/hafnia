#![cfg(feature = "nightly-features")]

use cavy_core::{cavy_errors, context::Context, source};

use proc_macro::{Delimiter, Group, LineColumn, TokenStream, TokenTree};

pub fn emit_diagnostics(
    errs: cavy_errors::ErrorBuf,
    spans: Vec<proc_macro::Span>,
    ctx: &mut Context,
) {
    for err in errs.0.into_iter() {
        emit_diagnostic(err, &spans, ctx);
    }
}

fn emit_diagnostic(
    err: Box<dyn cavy_errors::Diagnostic>,
    rspans: &[proc_macro::Span],
    ctx: &mut Context,
) {
    let level = translate_level(err.level());
    let msg = err.message(ctx);
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
    let line = line.linum;
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
pub fn stringify_whitespace(input: TokenStream) -> (String, Vec<proc_macro::Span>) {
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

        let col_diff = loc.column - self.col;
        self.col = loc.column;
        self.source.extend(std::iter::repeat(' ').take(col_diff));

        // Add the new string
        self.source += s;
        self.col += s.len();
    }
}
