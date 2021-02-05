use crate::{
    arch::Arch,
    cavy_errors::ErrorBuf,
    circuit::Circuit,
    context::{Context, CtxFmt},
    lowering, parser, scanner,
    session::Phase,
    source::{SrcId, SrcObject},
    target::ObjectCode,
};
use std::path::PathBuf;

pub fn compile_circuit<'a, 'ctx>(
    entry_point: SrcId,
    ctx: &'a mut Context<'ctx>,
) -> Result<Option<Circuit>, ErrorBuf> {
    let tokens = scanner::tokenize(entry_point, ctx)?;

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
    Ok(Some(circ))
}

pub fn compile_target<'a, 'ctx>(
    entry_point: SrcId,
    ctx: &'a mut Context<'ctx>,
) -> Result<Option<ObjectCode>, ErrorBuf> {
    compile_circuit(entry_point, ctx).map(|opt| opt.map(|circ| ctx.conf.target.from(&circ)))
}
