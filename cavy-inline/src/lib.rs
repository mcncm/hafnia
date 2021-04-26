//! This tiny crate just contains a macro for (Rust-)compile-time compilation of
//! Cavy code. It has to live in its own, separate crate, because Rust requires
//! crates to form a DAG. If this macro were included in the `cavy-macros`
//! crate, it would force a cyclic dependency between that crate and the cavy
//! library crate.

#![cfg_attr(feature = "nightly-features", feature(proc_macro_diagnostic))]
#![cfg_attr(feature = "nightly-features", feature(proc_macro_span))]

use cavy_core::{
    circuit::{Circuit, Gate},
    compile,
    context::Context,
    session::Config,
};
use proc_macro::TokenStream;
use quote::quote;

#[cfg(feature = "nightly-features")]
mod nightly;

/// Compile Cavy code at Rust-compile-time. This is the best and easiest way to
/// use Cavy as an embedded domain-specific language for quantum coprocessors
/// within Rust.
///
/// Currently, this macro provides no means to give non-default compiler
/// options.
#[proc_macro]
pub fn inline_cavy(input: TokenStream) -> TokenStream {
    let conf = Config::default();
    let mut ctx = Context::new(&conf);
    let src = stringify(input);
    let id = ctx.srcs.insert_input(&src.0);
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
                let spans = src.1;
                nightly::emit_diagnostics(errs, spans, &mut ctx);
                // Have to return something, or else get another error
                (quote! { Vec::<cavy::circuit::Gate>::new() }).into()
            }
        }
    }
}

/*
This is a bit of a funny hack. Without nightly-features, I only care about the
strinfified source code. With nightly-features, I also need rustc's `Span`s,
since these can't be reconstructed from integral source positions. Instead, we
hve to retain the original `Span`s and search through them again in order to
produce our error messages.

To make this work, we'll return a tuple from both of these functions. The
non-nightly one will only have a single element, the source itself. The nightly
one will have two elements: the second contains the original rustc spans,
retained for later use.
*/

// The variable *is* actually used
#[allow(unused_variables)]
#[cfg(not(feature = "nightly-features"))]
fn stringify(input: TokenStream) -> (&'static str,) {
    (stringify!(input),)
}

#[cfg(feature = "nightly-features")]
fn stringify(input: TokenStream) -> (String, Vec<proc_macro::Span>) {
    nightly::stringify_whitespace(input)
}

/// Turns a `Circuit` value into code that builds that literal circuit.
///
/// TODO better: to this by implementing `ToTokens` for `Circuit`.
fn quote_circuit(circ: Circuit) -> TokenStream {
    let gates = circ.into_iter().map(|gate| match gate {
        Gate::X(q) => quote! { ::cavy::circuit::Gate::X(#q) },
        Gate::T { tgt, conj } => quote! { ::cavy::circuit::Gate::T { tgt: #tgt, conj: #conj } },
        Gate::H(q) => quote! { ::cavy::circuit::Gate::H(#q) },
        Gate::Z(q) => quote! { ::cavy::circuit::Gate::Z(#q) },
        Gate::CX { tgt, ctrl } => quote! { ::cavy::circuit::Gate::CX { tgt: #tgt, ctrl: #ctrl } },
        Gate::SWAP { fst, snd } => quote! { ::cavy::circuit::Gate::Swap { fst: #fst, snd: #snd } },
        Gate::M(q) => quote! { ::cavy::circuit::Gate::M(#q) },
        Gate::Out(e) => {
            let cavy_core::circuit::IoOutGate { addr, name, elem } = *e;
            quote! {
                {
                    let e = ::cavy::circuit::IoOutGate {
                        #addr, #name, #elem
                    };
                    ::cavy::circuit::Gate::Ext(Box::new(e))
                }
            }
        }
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
