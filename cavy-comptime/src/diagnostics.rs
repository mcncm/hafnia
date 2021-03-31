use cavy_core::{cavy_errors, context::Context, source};

pub fn emit_diagnostics(errs: cavy_errors::ErrorBuf, ctx: &mut Context) {
    for err in errs.0.into_iter() {
        emit_diagnostic(err, ctx);
    }
}

fn emit_diagnostic(err: Box<dyn cavy_errors::Diagnostic>, ctx: &mut Context) {
    let level = translate_level(err.level());
    let msg = err.message(ctx);
    let diag = proc_macro::Diagnostic::new(level, msg);
    diag.emit();
}

/// Translate the internal Cavy diagnostic level to the proc macro `Level` api.
fn translate_level(level: &cavy_errors::DiagnosticLevel) -> proc_macro::Level {
    match level {
        cavy_errors::DiagnosticLevel::Error => proc_macro::Level::Error,
        cavy_errors::DiagnosticLevel::Warn => proc_macro::Level::Warning,
    }
}
