use crate::{arch::MeasurementMode, circuit::*};

use super::{mem::*, *};

impl<'a> Drop for Destructor<'a> {
    fn drop(&mut self) {
        while let Some(gate) = self.gates.pop() {
            self.circ.borrow_mut().push_qgate_inner(gate);
        }
    }
}

// This impl should deal with received *bits*.
impl<'m> CircAssembler<'m> {
    // This method needs mutable access to the circuit as well as the allocator.
    pub fn push_qgate(&mut self, gate: BaseGateQ, _st: &InterpreterState) {
        self.push_qgate_inner(GateQ::from(gate));
    }

    /// The inner function should *not* use the interpreter state, making it
    /// possible to call this from a reference destructor.
    fn push_qgate_inner(&mut self, gate: GateQ) {
        self.gate_buf.push(gate);
    }

    pub fn push_cgate(&mut self, gate: BaseGateC, _st: &InterpreterState) {
        self.push_cgate_inner(GateC::from(gate));
    }

    /// The inner function should *not* use the interpreter state, making it
    /// possible to call this from a reference destructor.
    fn push_cgate_inner(&mut self, gate: GateC) {
        self.gate_buf.push(gate);
    }

    // NOTE: maybe this method shouldn't be in this module, given that it's
    // translating from a place?
    pub fn push_io(&mut self, io: &IoStmtKind, st: &InterpreterState) {
        match io {
            IoStmtKind::In => todo!(),
            IoStmtKind::Out { place, symb } => {
                let bits = st.env.bits_at(place);
                for (i, &bit) in bits.cbits.iter().enumerate() {
                    let name = self.ctx.symbols[*symb].clone(); // blegh
                    let io = crate::circuit::IoOutGate {
                        addr: bit,
                        name,
                        elem: i,
                    };
                    self.gate_buf.push(Inst::Out(Box::new(io)));
                }
            }
        };
    }

    // NOTE: maybe this method shouldn't be in this module, given that it's
    // translating from a place?
    pub fn push_drop(&mut self, place: &Place, st: &InterpreterState) {
        let bits = st.env.bits_at(place);
        for qbit in bits.qbits {
            self.gate_buf.push(Inst::QFree(*qbit, FreeState::Dirty));
        }
        for cbit in bits.cbits {
            self.gate_buf.push(Inst::CFree(*cbit, FreeState::Dirty));
        }
    }

    /// Measure some qubits and store them in classical bits
    pub fn meas(&mut self, srcs: &[Qbit], tgts: &[Cbit], _st: &InterpreterState) {
        debug_assert!(srcs.len() == tgts.len());
        for (&src, &tgt) in srcs.iter().zip(tgts) {
            self.gate_buf.push(Inst::Meas(src, tgt));
        }
        self.free_meas(srcs);
    }

    /// Free a set of qubits after measurement
    pub fn free_meas(&mut self, addrs: &[Qbit]) {
        use MeasurementMode::*;
        let mode = self.ctx.conf.arch.meas_mode;
        // Hm, will the branch predictor take care of this for us?
        let free_state = match mode {
            Demolition => FreeState::Clean,
            Nondemolition => FreeState::Dirty,
            Dirty => FreeState::Dirty,
        };

        self.free(addrs.iter().copied(), free_state);
        for &addr in addrs {
            self.gate_buf.push(Inst::QFree(addr, free_state));
        }
    }
}
