//! This is the main library crate for the Cavy language compiler. It's used by
//! all drivers of the compiler, including the `cavyc` command-line interface
//! and the `pycavy` Python package. You can also use it as an ordinary Rust
//! crate, to include Cavy as a domain-specific language within your Rust
//! programs.

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
