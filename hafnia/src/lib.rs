// NOTE: I'm really not sure what must/should be public just yet. This is very
// much subject to change.
pub use hafnia_core::{arch, hafnia_errors, circuit, compile, context, session, target, util};

/// Compiles inline Hafnia code at Rust compile time. Hafnia programs that fail to
/// compile will fail Rust compilation. With a nightly compiler and the
/// `nightly-features` flag, Hafnia errors will also propagate out as Rust errors.
///
/// # Examples
///
/// ```compile_fail
/// hafnia::inline_hafnia! {
///     let x = ?true;
///     let y = x;
///     let z = x;
/// }
/// ```
#[cfg(feature = "inline")]
pub use hafnia_inline::inline_hafnia;

/// This top-level macro can be used to build a circuit from literal code, a
/// convenience when using Hafnia as an embedded language within Rust. For the
/// time being, there is no way to specify compiler options when using this
/// macro. Unlike `inline_hafnia`, this compiles at runtime.
#[macro_export]
macro_rules! hafnia {
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
