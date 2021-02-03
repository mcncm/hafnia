use crate::{
    arch::Arch,
    cavy_errors::ErrorBuf,
    context::{Context, CtxFmt},
    lowering, parser, scanner,
    session::Phase,
    source::SrcObject,
    target::ObjectCode,
};
use std::path::PathBuf;

pub fn compile<'a, 'ctx>(
    entry_point: PathBuf,
    ctx: &'a mut Context<'ctx>,
) -> Result<Option<ObjectCode>, ErrorBuf> {
    // There shouldn't be any validation happening here... Should be back up in
    // main(). Or maybe not--this might be the one kind of input validation that
    // can wait. After all, we won't know every file we need to read until we've
    // started reading *some* file.
    //
    // TODO Replace these unwraps.
    let id = ctx.srcs.insert_path(entry_point).unwrap();
    let tokens = scanner::tokenize(id, ctx)?;

    let ast = parser::parse(tokens, ctx)?;
    if ctx.conf.debug && ctx.last_phase() == &Phase::Parse {
        println!("{:#?}", ast);
        return Ok(None);
    }

    let mir = lowering::lower(ast, ctx)?;
    if ctx.conf.debug && ctx.last_phase() == &Phase::Typecheck {
        println!("{}", mir.fmt_with(&ctx));
        return Ok(None);
    }

    crate::analysis::check(&mir, ctx)?;

    let circ = crate::codegen::codegen(&mir, ctx);
    Ok(Some(ctx.conf.target.from(&circ)))

    // typecheck(&ctx, sess)?;
    //
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
