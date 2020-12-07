use crate::{
    arch::Arch,
    circuit::Circuit,
    errors::ErrorBuf,
    interpreter::Interpreter,
    parser::Parser,
    scanner::{Scanner, SourceCode},
    sys::Flags,
    target::Target,
};
use std::{error::Error, path::PathBuf};

pub fn compile<'a, C>(
    src: (String, String),
    _flags: Flags,
    arch: &'a Arch,
    target: &dyn Target<'a, ObjectCode = C>,
) -> Result<C, ErrorBuf> {
    let src = SourceCode {
        code: src.1.chars().peekable(),
        file: Some(src.0),
    };
    let tokens = Scanner::new(src).tokenize()?;
    let stmts = Parser::new(tokens).parse()?;
    let mut interpreter = Interpreter::new(&arch);
    interpreter.interpret(stmts)?;
    Ok(target.from(&interpreter))
}
