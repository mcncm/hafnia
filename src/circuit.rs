use crate::backend::{BackendSerializable, Qasm, QASM_VERSION};
use std::{
    collections::{HashSet, VecDeque},
    fmt,
};
use Gate::*;

pub type Qubit = usize;
/// These are gates from which most ordinary circuits will be built
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gate {
    X(Qubit),
    T { tgt: Qubit, conj: bool },
    H(Qubit),
    Z(Qubit),
    CX { tgt: Qubit, ctrl: Qubit },
}

impl Gate {
    pub fn qubits(&self) -> Vec<Qubit> {
        match self {
            X(tgt) => vec![*tgt],
            T { tgt, conj: _ } => vec![*tgt],
            H(tgt) => vec![*tgt],
            Z(tgt) => vec![*tgt],
            CX { ctrl, tgt } => vec![*ctrl, *tgt],
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
    pub fn controlled_on(self, ctrls: &HashSet<Qubit>) -> Vec<Gate> {
        let mut inner_gates = vec![self];
        for ctrl in ctrls.iter() {
            inner_gates = inner_gates
                .into_iter()
                .flat_map(|gate| gate.controlled_on_one(*ctrl))
                .collect::<Vec<Gate>>()
        }
        inner_gates
    }
}

impl BackendSerializable<Qasm> for Gate {
    #[rustfmt::skip]
    fn to_backend(&self) -> String {
        match self {
            X(tgt)           => format!("x q[{}];", tgt),
            T { tgt, conj }  => format!("{} q[{}];",
                                        if *conj { "tdg" } else { "t" },
                                        tgt),
            H(tgt)           => format!("h q[{}];", tgt),
            Z(tgt)           => format!("z q[{}];", tgt),
            CX { tgt, ctrl } => format!("cx q[{}], q[{}];", ctrl, tgt),
        }
    }
}

/// This is the main public circuit type
#[derive(Default, Debug)]
pub struct Circuit {
    pub circ_buf: VecDeque<Gate>,
    pub max_qubit: Option<usize>,
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

impl BackendSerializable<Qasm> for Circuit {
    fn to_backend(&self) -> String {
        let declaration = {
            if let Some(u) = self.max_qubit {
                format!("qreg q[{}];", u + 1)
            } else {
                String::from("")
            }
        };
        let gates = self
            .circ_buf
            .iter()
            .map(|gate| gate.to_backend())
            .collect::<Vec<String>>()
            .join("\n");
        format!(
            "OPENQASM {};\ninclude \"qelib1.inc\";\n{}\n{}\n",
            QASM_VERSION, declaration, gates
        )
    }
}

impl fmt::Display for Circuit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repr = self.to_backend();
        write!(f, "{}", repr)
    }
}
