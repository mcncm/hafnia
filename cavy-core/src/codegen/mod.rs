mod dynamic;

use crate::{circuit::Circuit, context::Context, mir::Mir};

pub fn translate(mir: &Mir, ctx: &Context) -> Circuit {
    let interp = dynamic::Interpreter::new(mir, ctx);
    interp.exec()
}
