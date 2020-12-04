use crate::{
    backend::{
        arch::Arch,
        target::{Qasm, TargetSerializable},
    },
    errors::Result,
    interpreter::Interpreter,
    parser::Parser,
    scanner::{Scanner, SourceCode},
    sys::Flags,
};
use std::{error::Error, path::PathBuf};

pub fn compile(src: (String, String), _flags: Flags, arch: &Arch) -> Result<String> {
    let src = SourceCode {
        code: src.1.chars().peekable(),
        file: Some(src.0),
    };
    let tokens = Scanner::new(src).tokenize().unwrap();
    let stmts = Parser::new(tokens).parse().unwrap();
    let mut interpreter = Interpreter::new(&arch);
    for stmt in stmts.into_iter() {
        interpreter.execute(&stmt)?;
    }

    let bindings_asm = interpreter.env.to_target();
    let circuit_asm: Qasm = interpreter.circuit.to_target();
    let asm = format!("//{}\n{}", bindings_asm.0, circuit_asm.0);
    Ok(asm)
}
