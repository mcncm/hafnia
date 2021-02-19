//! This tiny crate just contains a macro for (Rust-)compile-time compilation of
//! Cavy code. It has to live in its own, separate crate, because Rust requires
//! crates to form a DAG. If this macro were included in the `cavy-macros`
//! crate, it would force a cyclic dependency between that crate and the cavy
//! library crate.

use cavy_core::{
    circuit::{Circuit, Gate},
    compile,
    context::Context,
    session::Config,
};
use proc_macro::TokenStream;
use quote::quote;

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
    let src = input.to_string();
    let id = ctx.srcs.insert_input(&src);
    let circ = compile::compile_circuit(id, &mut ctx);
    // Can only get Ok(None) if compiler options ask to stop early
    let circ = circ.map(|circ| circ.unwrap());

    match circ {
        Ok(circ) => quote_circuit(circ),
        Err(_) => {
            panic!("Cavy compilation error!");
        }
    }
}

/// Turns a `Circuit` value into code that builds that literal circuit.
///
/// TODO better: to this by implementing `ToTokens` for `Circuit`.
fn quote_circuit(circ: Circuit) -> TokenStream {
    let Circuit {
        circ_buf,
        max_qubit,
    } = circ;

    let gates = circ_buf.iter().map(|gate| match gate {
        Gate::X(q) => quote! { ::cavy::circuit::Gate::X(#q) },
        Gate::T { tgt, conj } => quote! { ::cavy::circuit::Gate::T { tgt: #tgt, conj: #conj } },
        Gate::H(q) => quote! { ::cavy::circuit::Gate::H(#q) },
        Gate::Z(q) => quote! { ::cavy::circuit::Gate::Z(#q) },
        Gate::CX { tgt, ctrl } => quote! { ::cavy::circuit::Gate::CX { tgt: #tgt, ctrl: #ctrl } },
        Gate::M(q) => quote! { ::cavy::circuit::Gate::M(#q) },
    });

    let max_qubit = match max_qubit {
        Some(u) => quote! { Some(#u) },
        None => quote! { None },
    };

    let circuit_def = quote! {
        {
            let mut circ_buf = ::std::collections::VecDeque::new();
            #(circ_buf.push_back(#gates);)*
            let max_qubit = #max_qubit;
            ::cavy::circuit::Circuit {
                circ_buf,
                max_qubit,
            }
        }
    };

    circuit_def.into()
}
