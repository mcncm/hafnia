mod dynamic;

use crate::{circuit::CircuitBuf, context::Context, mir::Mir};

pub fn translate(mir: &Mir, ctx: &Context) -> CircuitBuf {
    let interp = dynamic::Interpreter::new(mir, ctx);
    interp.exec()
}
