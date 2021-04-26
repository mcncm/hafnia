use crate::circuit::Gate;

use super::*;

impl<'m> CircAssembler<'m> {
    // This method needs mutable access to the circuit as well as the allocator.
    pub fn push(&mut self, gate: Gate, _st: &InterpreterState) {
        self.gate_buf.push(gate);
    }
}
