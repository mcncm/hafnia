use crate::{
    arch::Arch,
    circuit::Circuit,
    errors::ErrorBuf,
    interpreter::Interpreter,
    parser::Parser,
    scanner::Scanner,
    source::SrcObject,
    sys::{CompilerPhase, Flags},
    target::Target,
    typecheck::typecheck,
};
use std::{error::Error, path::PathBuf};

pub fn compile<'a, 's, C>(
    src: SrcObject<'s>,
    flags: Flags,
    arch: &'a Arch,
    target: &dyn Target<'a, ObjectCode = C>,
) -> Result<Option<C>, ErrorBuf> {
    let last_phase = flags.phase_config.last_phase;

    if last_phase < CompilerPhase::Tokenize {
        return Ok(None);
    }
    let tokens = Scanner::new(&src).tokenize()?;

    if last_phase < CompilerPhase::Parse {
        return Ok(None);
    }
    let mut stmts = Parser::new(tokens).parse()?;

    if last_phase < CompilerPhase::Typecheck {
        return Ok(None);
    }

    if flags.phase_config.typecheck {
        typecheck(&mut stmts)?;
    }

    if last_phase < CompilerPhase::Evaluate {
        return Ok(None);
    }
    let mut interpreter = Interpreter::new(&arch);
    interpreter.interpret(stmts)?;
    Ok(Some(target.from(&interpreter)))
}
