use crate::circuit::Gate;

use super::*;

impl<'m> CircAssembler<'m> {
    // This method needs mutable access to the circuit as well as the allocator.
    pub fn push(&self, _gate: Gate, _st: &InterpreterState) {
        todo!()
    }
}
