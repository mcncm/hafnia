use crate::{arch::MeasurementMode, circuit::*, values::Value};

use super::{mem::*, *};

impl<'a> Drop for Destructor<'a> {
    fn drop(&mut self) {
        while let Some(gate) = self.gates.pop() {
            self.circ.borrow_mut().push_qgate_inner(gate.into());
        }
    }
}

// This impl should deal with received *bits*.
impl<'m> CircAssembler<'m> {
    // This method needs mutable access to the selfuit as well as the allocator.
    pub fn push_qgate<G>(&mut self, gate: G)
    where
        GateQ: From<G>,
    {
        self.push_qgate_inner(GateQ::from(gate));
    }

    /// The inner function should *not* use the interpreter state, making it
    /// possible to call this from a reference destructor.
    fn push_qgate_inner(&mut self, gate: GateQ) {
        self.gate_buf.push(gate);
    }

    pub fn push_cgate<G>(&mut self, gate: G)
    where
        GateC: From<G>,
    {
        let gate = GateC::from(gate);
        // I don't want to add a "classical swap" to any of the backends, so
        // simply expand this gate.
        if let BaseGate::C(BaseGateC::Swap(fst, snd)) = gate.base {
            for base in &[
                BaseGateC::Cnot {
                    ctrl: fst,
                    tgt: snd,
                },
                BaseGateC::Cnot {
                    ctrl: snd,
                    tgt: fst,
                },
                BaseGateC::Cnot {
                    ctrl: fst,
                    tgt: snd,
                },
            ] {
                self.push_cgate_inner(GateC {
                    ctrls: gate.ctrls.clone(),
                    base: base.clone().into(),
                })
            }
        } else {
            self.push_cgate_inner(gate);
        }
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

    pub fn free_qbit(&mut self, addr: Qbit, free_state: FreeState) {
        self.gate_buf.push(Inst::QFree(addr, free_state));
    }

    pub fn free_cbit(&mut self, addr: Cbit, free_state: FreeState) {
        self.gate_buf.push(Inst::CFree(addr, free_state));
    }

    // These measurement functions are iterating over bits, but that should not
    // be the job of this module.

    /// Measure some qubits and store them in classical bits
    pub fn meas(&mut self, srcs: &[Qbit], tgts: &[Cbit], _st: &InterpreterState) {
        debug_assert!(
            srcs.len() == tgts.len(),
            "got {} source qbits and {} target bits",
            srcs.len(),
            tgts.len()
        );
        for (&src, &tgt) in srcs.iter().zip(tgts) {
            self.gate_buf.push(Inst::Meas(src, tgt));
        }
        self.free_meas(srcs);
    }

    /// Free a set of qubits after measurement
    pub fn free_meas(&mut self, addrs: &[Qbit]) {
        use MeasurementMode::*;
        let mode = self.ctx.conf.arch.meas_mode;

        let free_state = match mode {
            Demolition => FreeState::Clean,
            // Maybe nondemolition should actually change the semantics of the
            // measurement operator?
            Dirty | Nondemolition => FreeState::Dirty,
        };
        self.free(addrs.iter().copied(), free_state);
        for &addr in addrs {
            self.gate_buf.push(Inst::QFree(addr, free_state));
        }
    }

    pub fn cnot_const(&mut self, obj: &BitSlice, value: &Value) {
        let const_bits = value.bits();
        if obj.cbits.is_empty() {
            for (idx, u) in obj.qbits.iter().enumerate() {
                if const_bits[idx] {
                    self.push_qgate(BaseGateQ::X(*u));
                }
            }
        } else if obj.qbits.is_empty() {
            for (idx, u) in obj.cbits.iter().enumerate() {
                if const_bits[idx] {
                    self.push_cgate(BaseGateC::Not(*u));
                }
            }
        } else {
            panic!("`cnot_const` must be called on all-classical or all-quantum lhs");
        }
    }

    // == basic gate mappers ==

    /*
    NOTE if anyone is reading this, I know this needs better abstraction(s).
    There's just *too much* code here. One day it will be beautiful and elegant,
    but today it just has to work.
    */

    /// Apply a Z gate to all the qubits
    pub fn map_phase(&mut self, obj: &BitSlice, sink: Option<&mut Vec<GateQ>>) {
        let phase = |u| BaseGateQ::Z(u);
        self.mapgate_sq(obj, phase, sink);
    }

    /// Apply an H gate to all the qubits
    pub fn map_hadamard(&mut self, obj: &BitSlice, sink: Option<&mut Vec<GateQ>>) {
        let split = |u| BaseGateQ::H(u);
        self.mapgate_sq(obj, split, sink)
    }

    /// NOT all the bits--classical and quantum--in one place
    pub fn map_not(&mut self, obj: &BitSlice, sink: Option<&mut Vec<GateQ>>) {
        let notq = |(_, u)| BaseGateQ::X(u);
        let notc = |(_, u)| BaseGateC::Not(u);
        // no `mapgate_sq` for both cbits and qbits yet
        if let Some(sink) = sink {
            let notq = util::tee(notq, sink);
            self.mapgate_single(obj, Some(notq), Some(notc));
        } else {
            self.mapgate_single(obj, Some(notq), Some(notc));
        }
    }

    /// CNOT all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    pub fn map_cnot(&mut self, ctrl: &BitSlice, tgt: &BitSlice, sink: Option<&mut Vec<GateQ>>) {
        let ctrlq = |(_, ctrl, tgt)| BaseGateQ::Cnot { ctrl, tgt };
        let ctrlc = |(_, ctrl, tgt)| BaseGateC::Cnot { ctrl, tgt };

        if let Some(sink) = sink {
            let ctrlq = util::tee(ctrlq, sink);
            self.mapgate_pair(ctrl, tgt, Some(ctrlq), Some(ctrlc));
        } else {
            self.mapgate_pair(ctrl, tgt, Some(ctrlq), Some(ctrlc));
        }
    }

    /// SWAP all the bits--classical and quantum--in two places, which should be
    /// of the same size.
    pub fn map_swap(&mut self, fst: &BitSlice, snd: &BitSlice, sink: Option<&mut Vec<GateQ>>) {
        let swapq = |(_, q1, q2)| BaseGateQ::Swap(q1, q2);
        let swapc = |(_, c1, c2)| BaseGateC::Swap(c1, c2);

        if let Some(sink) = sink {
            let swapq = util::tee(swapq, sink);
            self.mapgate_pair(fst, snd, Some(swapq), Some(swapc));
        } else {
            self.mapgate_pair(fst, snd, Some(swapq), Some(swapc));
        }
    }

    pub fn map_ccnot(
        &mut self,
        tgt: &BitSlice,
        fst: &BitSlice,
        fst_sign: bool,
        snd: &BitSlice,
        snd_sign: bool,
        sink: Option<&mut Vec<GateQ>>,
    ) {
        let quant = |(idx, fst, snd)| {
            let lhs = tgt.qbits[idx];
            // Correctness: fst != lhs, snd != lhs
            GateQ {
                ctrls: vec![(fst, fst_sign), (snd, snd_sign)],
                base: BaseGateQ::X(lhs),
            }
        };
        let class = |(idx, fst, snd)| {
            let lhs = tgt.cbits[idx];
            // The correctness assumption above doesn't hold here!
            GateC {
                ctrls: vec![(fst, snd_sign), (snd, fst_sign)],
                base: BaseGateC::Not(lhs).into(),
            }
        };

        if let Some(sink) = sink {
            let quant = util::tee(quant, sink);
            self.mapgate_pair(fst, snd, Some(quant), Some(class));
        } else {
            self.mapgate_pair(fst, snd, Some(quant), Some(class));
        }
    }
    // == teed gate mappers

    /// The main optionally-teed mapping function for the common use case of
    /// single-qubit gates
    pub fn mapgate_sq<F>(&mut self, obj: &BitSlice, f: F, sink: Option<&mut Vec<GateQ>>)
    where
        F: Fn(Qbit) -> BaseGateQ,
    {
        let fp = |(_, q)| f(q);

        match sink {
            Some(sink) => {
                let tee_f = util::tee(fp, sink);
                self.mapgate_single::<_, _, _, GateC>(obj, Some(tee_f), None::<fn(_) -> _>);
            }
            None => {
                self.mapgate_single::<_, _, _, GateC>(obj, Some(fp), None::<fn(_) -> _>);
            }
        }
    }

    /// The main optionally-teed mapping function for the common use case of
    /// two-qubit gates
    pub fn mapgate_tq<F>(
        &mut self,
        fst: &BitSlice,
        snd: &BitSlice,
        f: F,
        sink: Option<&mut Vec<BaseGateQ>>,
    ) where
        F: Fn(Qbit, Qbit) -> BaseGateQ,
    {
        let fp = |(_, q1, q2)| f(q1, q2);

        match sink {
            Some(sink) => {
                let tee_f = util::tee(fp, sink);
                self.mapgate_pair::<_, _, _, GateC>(fst, snd, Some(tee_f), None::<fn(_) -> GateC>);
            }
            None => {
                self.mapgate_pair::<_, _, _, GateC>(fst, snd, Some(fp), None::<fn(_) -> GateC>);
            }
        }
    }

    /// Map single-bit classical and quantum gates over an allocation
    pub fn mapgate_single<'a, Q, C, GQ, GC>(
        &'a mut self,
        obj: &BitSlice,
        quant: Option<Q>,
        class: Option<C>,
    ) where
        Q: FnMut((usize, Qbit)) -> GQ,
        C: FnMut((usize, Cbit)) -> GC,
        GateQ: From<GQ>,
        GateC: From<GC>,
    {
        if let Some(mut f) = quant {
            for (idx, qbit) in obj.qbits.iter().enumerate() {
                // NOTE: these copies shouldn't be necessary--this will be fixed
                // when arrays become iterable in Rust 2021.
                let gate = f((idx, *qbit));
                self.push_qgate(gate);
            }
        }

        if let Some(mut g) = class {
            for (idx, cbit) in obj.cbits.iter().enumerate() {
                let gate = g((idx, *cbit));
                self.push_cgate(gate);
            }
        }
    }

    /// Map two-bit classical and quantum gates over an allocation
    pub fn mapgate_pair<'a, Q, C, GQ, GC>(
        &'a mut self,
        fst: &BitSlice,
        snd: &BitSlice,
        quant: Option<Q>,
        class: Option<C>,
    ) where
        Q: FnMut((usize, Qbit, Qbit)) -> GQ,
        C: FnMut((usize, Cbit, Cbit)) -> GC,
        GateQ: From<GQ>,
        GateC: From<GC>,
    {
        if let Some(mut f) = quant {
            for ((idx, fst_qbit), snd_qbit) in fst.qbits.iter().enumerate().zip(snd.qbits.iter()) {
                let gate = f((idx, *fst_qbit, *snd_qbit));
                self.push_qgate(gate);
            }
        }

        if let Some(mut g) = class {
            for ((idx, fst_cbit), snd_cbit) in fst.cbits.iter().enumerate().zip(snd.cbits.iter()) {
                let gate = g((idx, *fst_cbit, *snd_cbit));
                self.push_cgate(gate);
            }
        }
    }

    /// Map two-bit classical-quantum gates over a pair of allocations. Unlike
    /// the previous two-allocation mapping function, this one has a definite
    /// direction: `ctrl` controls `snd`.
    pub fn mapgate_class_ctrl<'a, F>(&'a mut self, ctrl: &BitSlice, tgt: &BitSlice, f: Option<F>)
    where
        F: FnMut((usize, Cbit, Qbit)) -> BaseGateQ,
    {
        if let Some(mut f) = f {
            for ((idx, ctrl_bit), tgt_bit) in ctrl.cbits.iter().enumerate().zip(tgt.qbits.iter()) {
                let gate = f((idx, *ctrl_bit, *tgt_bit));
                let mut gate = <GateC>::from(gate);
                // FIXME this is sort of a stopgap to get the code to compile;
                // it's not really correct once we have classical uncomputation.
                gate.ctrls.push((*ctrl_bit, true));
                self.push_cgate(gate);
            }
        }
    }

    /// Free an allocation, calling a closure to determine how to free each bit.
    pub fn map_free<'a, Q, C>(&'a mut self, obj: &BitSlice, mut quant: Q, mut class: C)
    where
        Q: FnMut((usize, Qbit)) -> FreeState,
        C: FnMut((usize, Cbit)) -> FreeState,
    {
        for (idx, qbit) in obj.qbits.iter().enumerate() {
            self.free_qbit(*qbit, quant((idx, *qbit)));
        }

        for (idx, cbit) in obj.cbits.iter().enumerate() {
            self.free_cbit(*cbit, class((idx, *cbit)));
        }
    }
}
