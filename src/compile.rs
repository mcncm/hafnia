use crate::{
    backend::BackendSerializable,
    interpreter::Interpreter,
    parser::Parser,
    scanner::{Scanner, SourceCode},
    sys::Flags,
};
use std::{error::Error, path::PathBuf};

pub fn compile(src: (String, String), _flags: Flags) -> Result<String, Vec<Box<dyn Error>>> {
    let src = SourceCode {
        code: src.1.chars().peekable(),
        file: Some(src.0),
    };
    let tokens = Scanner::new(src).tokenize().unwrap();
    let stmts = Parser::new(tokens).parse().unwrap();
    let mut interpreter = Interpreter::new();
    for stmt in stmts.into_iter() {
        interpreter.execute(&stmt)?;
    }

    Ok(interpreter.circuit.to_backend())
}
