use crate::{
    arch::MeasurementMode,
    circuit::{CGate, Inst, PushInst, QGate},
};

use super::{mem::*, *};

impl<'m> CircAssembler<'m> {
    // This method needs mutable access to the circuit as well as the allocator.
    pub fn push(&mut self, gate: QGate, _st: &InterpreterState) {
        self.gate_buf.push(gate);
    }

    /// Measure some qubits and store them in classical bits
    pub fn meas(&mut self, srcs: &[Addr], tgts: &[Addr], _st: &InterpreterState) {
        for (&src, &tgt) in srcs.iter().zip(tgts) {
            self.gate_buf.push(Inst::Meas(src, tgt));
        }
        self.free_meas(srcs);
    }

    /// Free a set of qubits after measurement
    pub fn free_meas(&mut self, addrs: &[Addr]) {
        use MeasurementMode::*;
        let mode = self.ctx.conf.arch.meas_mode;
        // Hm, will the branch predictor take care of this for us?
        match mode {
            Demolition => {
                for &addr in addrs {
                    self.gate_buf.push(Inst::QFree(addr));
                }
                self.alloc.free_clean_quant(addrs.iter().copied());
            }
            Nondemolition => {
                // TODO: should reset qubit based on measurement result and
                // deallocate clean, if classical feedback is enabled.
                // Otherwise, deallocate dirty.
            }
            Dirty => {
                self.alloc.free_dirty_quant(addrs.iter().copied());
            }
        }
    }
}
