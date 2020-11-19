use std::{
    collections::{HashSet, VecDeque},
    fmt,
};

pub type Qubit = usize;
/// These are gates from which most ordinary circuits will be built
#[derive(Debug, Clone)]
pub enum Gate {
    X(Qubit),
    T { tgt: Qubit, conj: bool },
    H(Qubit),
    Z(Qubit),
    CX { tgt: Qubit, ctrl: Qubit },
}

use Gate::*;

impl Gate {
    fn qubits(&self) -> Vec<Qubit> {
        match self {
            X(tgt) => vec![*tgt],
            T { tgt, conj: _ } => vec![*tgt],
            H(tgt) => vec![*tgt],
            Z(tgt) => vec![*tgt],
            CX { ctrl, tgt } => vec![*ctrl, *tgt],
        }
    }

    fn conjugate(self) -> Gate {
        match self {
            T { tgt, conj } => T { tgt, conj: !conj },
            _ => self,
        }
    }

    #[rustfmt::skip]
    fn controlled_on(self, ctrl: Qubit) -> Vec<Gate> {
        match self {
            X(tgt) => vec![CX { ctrl, tgt }],
            T { tgt: _, conj: _ } => todo!(),
            H(_tgt) => todo!(),
            Z(tgt) => vec![
                Z(tgt),
                CX { ctrl, tgt },
                Z(tgt)
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
        }
    }

    /// Control on multiple qubits
    fn multi_controlled(self, ctrls: &HashSet<Qubit>) -> Vec<Gate> {
        let mut inner_gates = vec![self];
        for ctrl in ctrls.iter() {
            inner_gates = inner_gates
                .into_iter()
                .flat_map(|gate| gate.controlled_on(*ctrl))
                .collect::<Vec<Gate>>()
        }
        inner_gates
    }
}

/// This is the main public circuit type
#[derive(Default, Debug)]
pub struct Circuit {
    circ_buf: VecDeque<Gate>,
    qubits: HashSet<Qubit>,
}

impl Circuit {
    pub fn new() -> Self {
        Self::default()
    }

    /// This method embeds a gate into the circuit, controlled on the qubits
    /// given in its `ctrls` argument.
    pub fn push_back(&mut self, gate: Gate, ctrls: &HashSet<Qubit>) {
        // self.circ_buf.push_back(gate);
        let inner_gates = gate.multi_controlled(ctrls);
        for inner_gate in inner_gates.into_iter() {
            self.qubits.extend(inner_gate.qubits().iter());
            self.circ_buf.push_back(inner_gate);
        }
    }
}

impl fmt::Display for Circuit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut repr = String::new();
        for _ in 0..self.qubits.len() {
            repr.push_str(".\n");
        }
        write!(f, "{}", repr)
    }
}
