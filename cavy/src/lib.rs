// NOTE: I'm really not sure what must/should be public just yet. This is very
// much subject to change.
pub use cavy_core::{arch, cavy_errors, circuit, compile, context, session, target, util};

/// Compiles inline Cavy code at Rust compile time. Cavy programs that fail to
/// compile will fail Rust compilation. With a nightly compiler and the
/// `nightly-features` flag, Cavy errors will also propagate out as Rust errors.
///
/// # Examples
///
/// ```compile_fail
/// cavy::inline_cavy! {
///     let x = ?true;
///     let y = x;
///     let z = x;
/// }
/// ```
#[cfg(feature = "inline")]
pub use cavy_inline::inline_cavy;

/// This top-level macro can be used to build a circuit from literal code, a
/// convenience when using Cavy as an embedded language within Rust. For the
/// time being, there is no way to specify compiler options when using this
/// macro. Unlike `inline_cavy`, this compiles at runtime.
#[macro_export]
macro_rules! cavy {
    ($($src:tt)*) => {
        {
            default_context!(ctx);
            let id = ctx.srcs.insert_input(&stringify!($($src)*));
            let circ = $crate::compile::compile_circuit(id, &mut ctx);
            // Can only get Ok(None) if compiler options ask to stop early
            circ.map(|circ| circ.unwrap())
        }
    }
}
