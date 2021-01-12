use crate::{
    arch::Arch,
    cavy_errors::ErrorBuf,
    lowering,
    // circuit::Circuit,
    // interpreter::Interpreter,
    parser,
    scanner,
    session::{Phase, Session},
    source::SrcObject,
    // target::{ObjectCode, Target},
    typecheck::typecheck,
};
use std::path::PathBuf;

pub fn compile(entry_point: PathBuf, sess: &mut Session) -> Result<(), ErrorBuf> {
    // There shouldn't be any validation happening here... Should be back up in
    // main(). Or maybe not--this might be the one kind of input validation that
    // can wait. After all, we won't know every file we need to read until we've
    // started reading *some* file.
    //
    // TODO Replace these unwraps.
    let id = sess.sources.insert_path(entry_point).unwrap();
    let tokens = scanner::tokenize(id, sess)?;

    let ast = parser::parse(tokens, sess)?;
    if sess.config.debug && sess.last_phase() == &Phase::Parse {
        println!("{:#?}", ast);
    }

    let cfg = lowering::lower(ast, sess);
    if sess.config.debug && sess.last_phase() == &Phase::Typecheck {
        println!("{:#?}", cfg);
    }

    // typecheck(&ctx, sess)?;
    //
    Ok(())
    // if sess.config.phase_config.typecheck {
    //     let _ = typecheck(&mut stmts, &sess);
    // }

    // // I'll leave this phase undisturbed, since it is going to change
    // // dramatically, anyway.
    // let last_phase = sess.config.phase_config.last_phase;
    // if last_phase < Phase::Evaluate {
    //     crate::sys::exit(0);
    // }
    // let mut interpreter = Interpreter::new(sess.config.arch);
    // interpreter.interpret(stmts).unwrap();
    // sess.config.target.from(&interpreter)
}
