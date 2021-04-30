use crate::{
    arch::MeasurementMode,
    circuit::{BaseGateC, BaseGateQ, FreeState, GateC, GateQ, Inst},
};

use super::{mem::*, *};

// This impl should deal with received *bits*.
impl<'m> CircAssembler<'m> {
    // This method needs mutable access to the circuit as well as the allocator.
    pub fn push_qgate(&mut self, gate: BaseGateQ, _st: &InterpreterState) {
        self.gate_buf.push(GateQ::from(gate));
    }

    pub fn push_cgate(&mut self, gate: BaseGateC, _st: &InterpreterState) {
        self.gate_buf.push(GateC::from(gate));
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
    pub fn meas(&mut self, srcs: &[Addr], tgts: &[Addr], _st: &InterpreterState) {
        debug_assert!(srcs.len() == tgts.len());
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
        let free_state = match mode {
            Demolition => FreeState::Clean,
            Nondemolition => FreeState::Dirty,
            Dirty => FreeState::Dirty,
        };

        self.alloc.free_quant(addrs.iter().copied(), free_state);
        for &addr in addrs {
            self.gate_buf.push(Inst::QFree(addr, free_state));
        }
    }
}
