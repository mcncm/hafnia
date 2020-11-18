use std::{
    collections::{HashSet, VecDeque},
    fmt,
};

type Qubit = usize;
type NdArray = ();

/// This is the common trait that any gate type must derive to be pushed to a
/// backend. Making `Gate` a trait makes it possible to include some
/// less-conventional operations like probabilistic gates.
pub trait Gate {
    fn qubits(&self) -> Vec<Qubit>;

    fn to_matrix(&self) -> NdArray {
        unimplemented!();
    }
}

/// These are gates from which most ordinary circuits will be built
pub enum CommonGate {
    X(Qubit),
    T(Qubit),
    H(Qubit),
    Z(Qubit),
    CX(Qubit, Qubit),
}

impl Gate for CommonGate {
    fn qubits(&self) -> Vec<Qubit> {
        match self {
            Self::X(qubit) => vec![*qubit],
            Self::T(qubit) => vec![*qubit],
            Self::H(qubit) => vec![*qubit],
            Self::Z(qubit) => vec![*qubit],
            Self::CX(control, target) => vec![*control, *target],
        }
    }
}

/// This is the main public circuit type
#[derive(Default)]
pub struct Circuit {
    circ_buf: VecDeque<Box<dyn Gate>>,
    qubits: HashSet<Qubit>,
}

impl Circuit {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_back(&mut self, gate: Box<dyn Gate>) {
        self.qubits.extend(gate.qubits());
        self.circ_buf.push_back(gate);
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
