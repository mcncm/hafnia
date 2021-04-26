use crate::{ast::FnId, store::Index};
use crate::{
    context::SymbolId,
    target::{qasm::Qasm, IntoTarget, Target},
    types::TypeSize,
};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    vec::IntoIter,
};
use Gate::*;

/// This type alias identifies qubits with their numerical indices
pub type VirtAddr = usize;

pub type PhysAddr = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IoOutGate {
    pub addr: VirtAddr,
    /// Name of the ext location. Maybe this could be a `SymbolId`--but that
    /// would necessitate refactoring the `target` api, and I really don't want
    /// to go there.
    pub name: String,
    /// Bit of the ext location
    pub elem: usize,
}

/// These are gates from which most ordinary circuits will be built
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gate {
    X(VirtAddr),
    T {
        tgt: VirtAddr,
        conj: bool,
    },
    H(VirtAddr),
    Z(VirtAddr),
    CX {
        tgt: VirtAddr,
        ctrl: VirtAddr,
    },
    SWAP {
        fst: VirtAddr,
        snd: VirtAddr,
    },

    // Not-really-gate gates
    /// Measurement "gate"
    M(VirtAddr),
    /// Output "gate"
    Out(Box<IoOutGate>),
}

impl Gate {
    pub fn qubits(&self) -> Vec<VirtAddr> {
        match self {
            X(tgt) => vec![*tgt],
            T { tgt, conj: _ } => vec![*tgt],
            H(tgt) => vec![*tgt],
            Z(tgt) => vec![*tgt],
            CX { ctrl, tgt } => vec![*ctrl, *tgt],
            SWAP { fst, snd } => vec![*fst, *snd],
            M(tgt) => vec![*tgt],
            Out(_) => vec![],
        }
    }

    pub fn conjugate(self) -> Gate {
        match self {
            T { tgt, conj } => T { tgt, conj: !conj },
            _ => self,
        }
    }

    #[rustfmt::skip]
    fn controlled_on_one(self, ctrl: VirtAddr) -> Vec<Gate> {
        match self {
            X(tgt) => vec![CX { ctrl, tgt }],
            T { tgt: _, conj: _ } => todo!(),
            H(_tgt) => todo!(),
            Z(tgt) => vec![
                H(tgt),
                CX { ctrl, tgt },
                H(tgt)
            ],
            // This is just applying a well-known identity for CCX.
            CX { ctrl: inner_ctrl, tgt } => vec![
                H(tgt),
                CX { ctrl: inner_ctrl, tgt },
                T { tgt, conj: true},
                CX { ctrl, tgt },
                T { tgt, conj: false },
                CX { ctrl: inner_ctrl, tgt },
                T { tgt, conj: true},
                CX { ctrl, tgt },
                T { tgt: inner_ctrl, conj: false },
                T { tgt, conj: false },
                CX { ctrl, tgt: inner_ctrl },
                H(tgt),
                T { tgt: ctrl, conj: false },
                T { tgt: inner_ctrl, conj: true },
                CX { ctrl, tgt: inner_ctrl },
            ],
            SWAP{ .. } => todo!(),
            M(_) => todo!(),
            Out(_) => todo!(),
        }
    }

    /// Control on multiple qubits
    pub fn controlled_on(self, ctrls: Box<dyn Iterator<Item = VirtAddr>>) -> Vec<Gate> {
        let mut inner_gates = vec![self];
        for ctrl in ctrls {
            inner_gates = inner_gates
                .into_iter()
                .flat_map(|gate| gate.controlled_on_one(ctrl))
                .collect::<Vec<Gate>>()
        }
        inner_gates
    }
}

impl IntoTarget<Qasm> for Gate {
    #[rustfmt::skip]
    fn into_target(self, _target: &Qasm) -> String {
        match self {
            X(tgt)            => format!("x q[{}];", tgt),
            T { tgt, conj }   => format!("{} q[{}];",
                                         if conj { "tdg" } else { "t" },
                                         tgt),
            H(tgt)            => format!("h q[{}];", tgt),
            Z(tgt)            => format!("z q[{}];", tgt),
            CX { tgt, ctrl }  => format!("cx q[{}], q[{}];", ctrl, tgt),
            SWAP { .. }       => todo!(),
            M(tgt)            => format!("measure q[{}] -> c[{}];", tgt, tgt),
            Out(io)            => {
                // TODO OpenQASM doesn't support this kind of operation, does it? What
                // should we do here?
                format!("// copy c[{}] __out_{}[{}] ", io.addr, io.name, io.elem)
            },
        }
    }
}

/// A simple circuit struct. This backend data structure keeps changing, but it
#[derive(Debug)]
pub struct Circuit {
    gates: Vec<Gate>,
    max_qbit: usize,
    max_cbit: usize,
}

impl Circuit {
    pub fn new() -> Self {
        Self {
            gates: Vec::new(),
            max_qbit: 0,
            max_cbit: 0,
        }
    }

    pub fn max_qubit(&self) -> Option<usize> {
        Some(self.max_qbit)
    }

    pub fn into_iter(self) -> CircuitStream {
        CircuitStream {
            gates: self.gates.into_iter(),
        }
    }
}

pub struct CircuitStream {
    gates: IntoIter<Gate>,
}

impl Iterator for CircuitStream {
    type Item = Gate;

    fn next(&mut self) -> Option<Self::Item> {
        self.gates.next()
    }
}

// === Formatting implementations

impl std::fmt::Display for Gate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            X(q) => write!(f, "X {}", q),
            T { tgt, conj } => {
                let conj = if *conj { "*" } else { "" };
                write!(f, "T{} {}", conj, tgt)
            }
            H(q) => write!(f, "H {}", q),
            Z(q) => write!(f, "Z {}", q),
            CX { tgt, ctrl } => write!(f, "CX {} {}", ctrl, tgt),
            SWAP { fst, snd } => write!(f, "SWAP {} {}", fst, snd),
            M(q) => write!(f, "M {}", q),
            Out(e) => write!(f, "{} -> {:?}[{}]", e.addr, e.name, e.elem),
        }
    }
}
