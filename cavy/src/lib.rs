#![allow(clippy::new_without_default)]
#![allow(unused_imports)]
#![allow(dead_code)]

pub mod alloc;
pub mod analysis;
pub mod arch;
pub mod ast;
pub mod cavy_errors;
pub mod circuit;
pub mod codegen;
pub mod compile;
pub mod context;
pub mod mir;
pub mod session;
// pub mod environment;
// pub mod functions;
// pub mod interpreter;
// pub mod inference;
pub mod parser;
// pub mod qram;
pub mod scanner;
// pub mod session;
pub mod lowering;
pub mod num;
pub mod source;
pub mod store;
pub mod sys;
pub mod target;
pub mod token;
pub mod types;
pub mod values;

/// This top-level macro can be used to build a circuit from literal code, a
/// convenience when using Cavy as an embedded language within Rust. For the
/// time being, there is no way to specify compiler options when using this
/// macro.
// NOTE This is not how this macro ought to work! It should be implemented as a
// proc macro that actually compiles the Cavy source, and returns code to build
// a literal circuit. This will make it possible to report errors at (Rust)
// compile time. But there is a wrinkle: if we naively put that macro into
// `cavy_macros`, there will be a circular dependency since, in order to compile
// Cavy code at Rust compile time, we need access to the `cavy` crate. One
// solution to this problem is to factor the `cavy` crate into a "core" library
// and a public-facing crate that re-exports its contents along with the macro.
// This will be a fantastic convenience feature, but I've done enough yak
// shaving for right now.
#[macro_export]
macro_rules! cavy {
    ($($src:tt)*) => {
        {
            let conf = $crate::session::Config::default();
            let mut ctx = $crate::context::Context::new(&conf);

            let id = ctx.srcs.insert_input(&stringify!($($src)*));
            let circ = $crate::compile::compile_circuit(id, &mut ctx);
            // Can only get Ok(None) if compiler options ask to stop early
            circ.map(|circ| circ.unwrap())
        }
    }
}
