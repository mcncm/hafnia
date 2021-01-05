use crate::target::{qasm::Qasm, IntoTarget, Target};
use std::{
    collections::{HashSet, VecDeque},
    fmt,
};
use Gate::*;

/// This type alias identifies qubits with their numerical indices
pub type Qubit = usize;

/// These are gates from which most ordinary circuits will be built
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gate {
    X(Qubit),
    T { tgt: Qubit, conj: bool },
    H(Qubit),
    Z(Qubit),
    CX { tgt: Qubit, ctrl: Qubit },
    // Measurement "gate"
    M(Qubit),
}

impl Gate {
    pub fn qubits(&self) -> Vec<Qubit> {
        match self {
            X(tgt) => vec![*tgt],
            T { tgt, conj: _ } => vec![*tgt],
            H(tgt) => vec![*tgt],
            Z(tgt) => vec![*tgt],
            CX { ctrl, tgt } => vec![*ctrl, *tgt],
            M(tgt) => vec![*tgt],
        }
    }

    pub fn conjugate(self) -> Gate {
        match self {
            T { tgt, conj } => T { tgt, conj: !conj },
            _ => self,
        }
    }

    #[rustfmt::skip]
    fn controlled_on_one(self, ctrl: Qubit) -> Vec<Gate> {
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
            M(_) => todo!(),
        }
    }

    /// Control on multiple qubits
    pub fn controlled_on(self, ctrls: Box<dyn Iterator<Item = Qubit>>) -> Vec<Gate> {
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
    fn into_target(&self, _target: &Qasm) -> String {
        match self {
            X(tgt)           => format!("x q[{}];", tgt),
            T { tgt, conj }  => format!("{} q[{}];",
                                        if *conj { "tdg" } else { "t" },
                                        tgt),
            H(tgt)           => format!("h q[{}];", tgt),
            Z(tgt)           => format!("z q[{}];", tgt),
            CX { tgt, ctrl } => format!("cx q[{}], q[{}];", ctrl, tgt),
            M(tgt)           => format!("measure q[{}] -> c[{}];", tgt, tgt)
        }
    }
}

/// This is the main public circuit type
#[derive(Default, Debug)]
pub struct Circuit {
    pub circ_buf: VecDeque<Gate>,
    pub max_qubit: Option<Qubit>,
}

impl Circuit {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_back(&mut self, gate: Gate) {
        use std::cmp;
        // This unwrap is safe as long as all gates act on *some* qubit.
        let max_in_gate = *gate.qubits().iter().max().unwrap();
        self.max_qubit = match self.max_qubit {
            Some(u) => Some(cmp::max(u, max_in_gate)),
            None => Some(max_in_gate),
        };
        self.circ_buf.push_back(gate);
    }
}

impl fmt::Display for Circuit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::target::{qasm::Qasm, IntoTarget};
        let backend = Qasm {};
        let repr: String = self.into_target(&backend);
        write!(f, "{}", repr)
    }
}
