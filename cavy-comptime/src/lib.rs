//! This tiny crate just contains a macro for (Rust-)compile-time compilation of
//! Cavy code. It has to live in its own, separate crate, because Rust requires
//! crates to form a DAG. If this macro were included in the `cavy-macros`
//! crate, it would force a cyclic dependency between that crate and the cavy
//! library crate.

#![cfg_attr(feature = "nightly-features", feature(proc_macro_diagnostic))]
#![cfg_attr(feature = "nightly-features", feature(proc_macro_span))]

use cavy_core::{
    circuit::{Gate, Lir},
    compile,
    context::Context,
    session::Config,
};
use proc_macro::TokenStream;
use quote::quote;

#[cfg(feature = "nightly-features")]
mod diagnostics;

#[cfg(feature = "nightly-features")]
use proc_macro::{LineColumn, TokenTree};

/// Compile Cavy code at Rust-compile-time. This is the best and easiest way to
/// use Cavy as an embedded domain-specific language for quantum coprocessors
/// within Rust.
///
/// Currently, this macro provides no means to give non-default compiler
/// options.
#[proc_macro]
pub fn cavy_comptime(input: TokenStream) -> TokenStream {
    let conf = Config::default();
    let mut ctx = Context::new(&conf);
    let src = stringify(input);
    let id = ctx.srcs.insert_input(&src);
    let circ = compile::compile_circuit(id, &mut ctx);
    // Can only get Ok(None) if compiler options ask to stop early
    let circ = circ.map(|circ| circ.unwrap());

    #[allow(unused_variables)]
    match circ {
        Ok(circ) => quote_circuit(circ),
        Err(errs) => {
            #[cfg(not(feature = "nightly-features"))]
            {
                panic!("Cavy compilation error!");
            }

            #[cfg(feature = "nightly-features")]
            {
                diagnostics::emit_diagnostics(errs, &mut ctx);
                (quote! { Vec::new() }).into()
            }
        }
    }
}

/// Turns a `Circuit` value into code that builds that literal circuit.
///
/// TODO better: to this by implementing `ToTokens` for `Circuit`.
fn quote_circuit(circ: Lir) -> TokenStream {
    let gates = circ.iter().map(|gate| match gate {
        Gate::X(q) => quote! { ::cavy::circuit::Gate::X(#q) },
        Gate::T { tgt, conj } => quote! { ::cavy::circuit::Gate::T { tgt: #tgt, conj: #conj } },
        Gate::H(q) => quote! { ::cavy::circuit::Gate::H(#q) },
        Gate::Z(q) => quote! { ::cavy::circuit::Gate::Z(#q) },
        Gate::CX { tgt, ctrl } => quote! { ::cavy::circuit::Gate::CX { tgt: #tgt, ctrl: #ctrl } },
        Gate::SWAP { fst, snd } => quote! { ::cavy::circuit::Gate::Swap { fst: #fst, snd: #snd } },
        Gate::M(q) => quote! { ::cavy::circuit::Gate::M(#q) },
    });

    let circuit_def = quote! {
        {
            let mut circ_buf = Vec::new();
            #(circ_buf.push(#gates);)*
            circ_buf
        }
    };

    circuit_def.into()
}

#[cfg(not(feature = "nightly-features"))]
fn stringify(input: TokenStream) -> String {
    input.to_string()
}

#[cfg(feature = "nightly-features")]
fn stringify(input: TokenStream) -> String {
    input.to_string()
}

