//! OpenQASM target, the default "assembly" backend most useful for interop with
//! scripting language tools.

use super::*;

use crate::circuit::{BaseGateQ, GateQ, Inst};
use std::fmt;

/// There is a version 3 of QASM, but we’re only going to use 2.0 for now, since
/// this is what Cirq supports.
pub const QASM_VERSION: &str = "2.0";

/// The Qasm object code type is just a wrapper around a String.
pub struct Qasm();

impl Qasm {
    fn headers(&self) -> String {
        format!("OPENQASM {};\ninclude \"qelib1.inc\";", QASM_VERSION)
    }

    fn emit_inst(&self, inst: &Inst, f: &mut fmt::Formatter, ctx: &Context) -> fmt::Result {
        // FIXME this is a hack! These gates should be replaced at a point
        // "higher up" that knows about the structure of the program. This isn't
        // representation; it's content.
        match inst {
            Inst::QGate(GateQ { ctrls, base }) => {
                if !ctrls.is_empty() {
                    panic!("QASM doesn't support multiple controls");
                } else {
                    use BaseGateQ::*;
                    match base {
                        Swap(fst, snd) => {
                            for gate in &[
                                Cnot {
                                    ctrl: *fst,
                                    tgt: *snd,
                                },
                                Cnot {
                                    ctrl: *snd,
                                    tgt: *fst,
                                },
                                Cnot {
                                    ctrl: *fst,
                                    tgt: *snd,
                                },
                            ] {
                                writeln!(f, "{};", gate.fmt_with(self))?;
                            }
                            Ok(())
                        }
                        gate => writeln!(f, "{};", gate.fmt_with(self)),
                    }
                }
            }
            inst => write!(f, "{}", inst.fmt_with(&(self, ctx))),
        }
    }
}

impl FmtWith<Qasm> for BaseGateQ {
    fn fmt(&self, _qasm: &Qasm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BaseGateQ::*;
        match self {
            X(tgt) => write!(f, "x q[{}]", tgt),
            H(tgt) => write!(f, "h q[{}]", tgt),
            Z(tgt) => write!(f, "z q[{}]", tgt),
            T(tgt) => write!(f, "t q[{}]", tgt),
            TDag(tgt) => write!(f, "tdg q[{}]", tgt),
            S(tgt) => write!(f, "s q[{}]", tgt),
            SDag(tgt) => write!(f, "sdg q[{}]", tgt),
            Phase(_tgt, _phase) => todo!(),
            Cnot { ctrl, tgt } => write!(f, "cx q[{}], q[{}]", ctrl, tgt),
            Swap { .. } => unimplemented!("OpenQASM 2.0 doesn't support SWAP"),
        }
    }
}

impl FmtWith<Qasm> for GateQ {
    fn fmt(&self, qasm: &Qasm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BaseGateQ::*;
        match (self.ctrls.len(), self.base) {
            (0, _) => write!(f, "{}", self.base.fmt_with(qasm)),
            (1, X(tgt)) => {
                if !self.ctrls[0].1 {
                    unimplemented!();
                }
                write!(f, "cx q[{}], q[{}]", self.ctrls[0].0, tgt)
            }
            // Unsupported gate
            _ => unreachable!(),
        }
    }
}

impl<'c> FmtWith<(&Qasm, &Context<'c>)> for Inst {
    fn fmt(&self, (qasm, ctx): &(&Qasm, &Context), f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Inst::QGate(g) => writeln!(f, "{};", g.fmt_with(qasm)),
            Inst::Meas(src, tgt) => writeln!(f, "measure q[{}] -> c[{}];", src, tgt),
            Inst::Io(io) => {
                // TODO OpenQASM doesn't support this kind of operation, does it? What
                // should we do here?
                writeln!(
                    f,
                    "// copy c[{}] __out_{}[{}]; ",
                    io.addr,
                    io.channel.fmt_with(ctx),
                    io.elem
                )
            }
            _ => Ok(()),
        }
    }
}

impl<'a> FmtWith<(&Qasm, &Context<'a>)> for CircuitBuf {
    // It's too bad that this doesn't consume the circuit. I should find a
    // way to do that, by calling `circ.into_iter()` instead of implementing
    // `FmtWith<Qasm>` for CircuitBuf. Plus, the headers logically "belong
    // to" the target data, not the circuit. The problem is that, there's no
    // way to format the iterator, because `.next()` mutates it.
    fn fmt(
        &self,
        (qasm, ctx): &(&Qasm, &Context),
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(f, "{}", qasm.headers())?;
        writeln!(f, "qreg q[{}];", self.qbit_size())?;
        writeln!(f, "creg c[{}];", self.cbit_size())?;
        for inst in self.iter() {
            qasm.emit_inst(inst, f, ctx)?;
        }
        Ok(())
    }
}

impl Target for Qasm {
    fn from(&self, circ: CircuitBuf, ctx: &Context) -> ObjectCode {
        format!("{}", circ.fmt_with(&(self, ctx)))
    }
}
