mod dynamic;

use crate::{circuit::CircuitBuf, context::Context, mir::Mir};

pub fn translate(mir: &Mir, ctx: &Context) -> CircuitBuf {
    dynamic::translate(mir, ctx)
}
