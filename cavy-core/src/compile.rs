use crate::{
    arch::Arch,
    cavy_errors::ErrorBuf,
    circuit::CircuitBuf,
    context::{Context, CtxDisplay, CtxFmt},
    lowering, parser, scanner,
    session::Phase,
    source::{SrcId, SrcObject},
    target::ObjectCode,
};
use std::path::PathBuf;

/// Compile a program to a quantum(-classical) circuit representation.
pub fn compile_circuit(
    entry_point: SrcId,
    ctx: &mut Context,
) -> Result<Option<CircuitBuf>, ErrorBuf> {
    let tokens = scanner::tokenize(entry_point, ctx)?;

    let ast = parser::parse(tokens, ctx)?;
    if ctx.last_phase() == &Phase::Parse {
        if ctx.conf.debug {
            println!("{:#?}", ast);
        }
        return Ok(None);
    }

    let mut mir = lowering::lower(ast, ctx)?;
    if ctx.last_phase() == &Phase::Typecheck {
        if ctx.conf.debug {
            println!("{}", mir.fmt_with(&ctx));
        }
        return Ok(None);
    }

    crate::analysis::check(&mir, ctx)?;
    if ctx.last_phase() == &Phase::Analysis {
        return Ok(None);
    }

    crate::opt::optimize(&mut mir, ctx);
    if ctx.last_phase() == &Phase::Optimization {
        if ctx.conf.debug {
            println!("{}", mir.fmt_with(&ctx));
        }
        return Ok(None);
    }

    let circ = crate::codegen::translate(&mir, ctx);
    if ctx.last_phase() == &Phase::Translation {
        if ctx.conf.debug {
            println!("{:?}", circ);
        }
        return Ok(None);
    }

    Ok(Some(circ))
}

/// Compile a program to object code by serializing a circuit representation.
/// Note that this might not be the right approach in the long run if
/// recursion/infinite loops are enabled as there will be programs with
/// finite-sized object code representations, but infinite circuits.
pub fn compile_target(
    entry_point: SrcId,
    ctx: &mut Context,
) -> Result<Option<ObjectCode>, ErrorBuf> {
    compile_circuit(entry_point, ctx).map(|opt| opt.map(|circ| ctx.conf.target.from(circ)))
}
