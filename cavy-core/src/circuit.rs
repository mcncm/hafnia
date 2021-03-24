use crate::ast::FnId;
use crate::target::{qasm::Qasm, IntoTarget, Target};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};
use Gate::*;

/// This type alias identifies qubits with their numerical indices
pub type VirtAddr = usize;

/// These are gates from which most ordinary circuits will be built
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gate {
    X(VirtAddr),
    T { tgt: VirtAddr, conj: bool },
    H(VirtAddr),
    Z(VirtAddr),
    CX { tgt: VirtAddr, ctrl: VirtAddr },
    SWAP { fst: VirtAddr, snd: VirtAddr },
    // Measurement "gate"
    M(VirtAddr),
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
    fn into_target(&self, _target: &Qasm) -> String {
        match self {
            X(tgt)            => format!("x q[{}];", tgt),
            T { tgt, conj }   => format!("{} q[{}];",
                                         if *conj { "tdg" } else { "t" },
                                         tgt),
            H(tgt)            => format!("h q[{}];", tgt),
            Z(tgt)            => format!("z q[{}];", tgt),
            CX { tgt, ctrl }  => format!("cx q[{}], q[{}];", ctrl, tgt),
            SWAP { .. }       => todo!(),
            M(tgt)            => format!("measure q[{}] -> c[{}];", tgt, tgt)
        }
    }
}

/// A terrible name that will be fixed later: each of the "things" that take
/// place, namely gates and procedure calls.
#[derive(Debug)]
pub enum Instruction {
    Gate(Gate),
    FnCall(FnId, Vec<VirtAddr>),
}

/// The type of a single procedure in the low-level circuit IR. For now, these
/// are *finite* lists of gates and procedure calls. In the future, they will
/// look more like some kind of stream.
///
/// FIXME Also, this is not a great name for this struct, and it's likely to change.
#[derive(Default, Debug)]
pub struct LirGraph {
    /// The number of qubits used in calling this procedure. This may one day be
    /// split into `qargs` and `cargs` or something like this, essentially
    /// typing the parameters.
    ///
    /// For now, we're assuming this to be finite.
    pub args: usize,
    /// The number of other qubits used by the procedure. The circuit width of
    /// the procedure, ignoring subroutines, is then `args + ancillae`.
    pub ancillae: usize,
    /// All the instructions of the compiled subroutine. Note that this is, for
    /// now, a finite structure. That is likely to change.
    pub instructions: Vec<Instruction>,
}

/// This is the main public circuit type
///
/// NOTE should probably rename this to `Lir` or something, and name an actual
/// (physically-addressed) circuit as `Circuit`.
#[derive(Default, Debug)]
pub struct Circuit {
    pub graphs: HashMap<FnId, LirGraph>,
    pub entry_point: FnId,
}

impl Circuit {
    pub fn max_qubit(&self) -> Option<usize> {
        /// FIXME This is manifestly wrong. Although maybe this struct shouldn't
        /// have any such idea, anyway.
        None
    }

    pub fn iter(&self) -> CircuitStream {
        CircuitStream::new(self)
    }
}

pub struct CircuitStream<'c> {
    circ: &'c Circuit,
    active: std::slice::Iter<'c, Instruction>,
    // FIXME this implementation is a problem for arbitrary mutual recursion,
    // as the stack will grow indefinitely.
    stack: Vec<std::slice::Iter<'c, Instruction>>,
}

impl<'c> CircuitStream<'c> {
    fn new(circ: &'c Circuit) -> Self {
        let gr = &circ.graphs[&circ.entry_point];
        let active = gr.instructions.iter();
        Self {
            circ,
            active,
            stack: vec![],
        }
    }
}

impl<'c> Iterator for CircuitStream<'c> {
    type Item = &'c Gate;

    fn next(&mut self) -> Option<Self::Item> {
        match self.active.next() {
            None => None,
            Some(Instruction::Gate(gate)) => Some(gate),
            Some(Instruction::FnCall(_, _)) => todo!(),
        }
    }
}
