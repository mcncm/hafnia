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

/// This type alias identifies qubits with their numerical indices
pub type Addr = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IoOutGate {
    /// Classical address to read from
    pub addr: Addr,
    /// Name of the ext location. Maybe this could be a `SymbolId`--but that
    /// would necessitate refactoring the `target` api, and I really don't want
    /// to go there.
    pub name: String,
    /// Bit of the ext location
    pub elem: usize,
}

// NOTE: if you change the layout of this enum, its method `qubits` is sure to
// break, on account of the pointer arithmetic inside it.
/// These are gates from which most ordinary circuits will be built.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum QGate {
    X(Addr),
    T { tgt: Addr, conj: bool },
    H(Addr),
    Z(Addr),
    CX { ctrl: Addr, tgt: Addr },
    SWAP { fst: Addr, snd: Addr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum CGate {
    Not(Addr),
    /// The first address is the source bit; the second is the target bit
    Copy(Addr, Addr),
    /// The first address is the source bit; the second is the target bit
    Cnot(Addr, Addr),
    /// Control a quantum gate on a classical bit
    Control(Addr, Box<QGate>),
}

/// The simple instructions that make up the low-level circuit stream
/// representation
#[derive(Debug)]
pub enum Inst {
    /// Bring up a bit rail
    CInit(Addr),
    /// Set down a bit rail
    CFree(Addr),
    /// Bring up a qubit rail
    QInit(Addr),
    /// Set down a qubit rail
    QFree(Addr),
    /// A quantum gate
    QGate(QGate),
    /// A classical gate
    CGate(CGate),
    /// Measurement: the first address is the qubit measured; the second is the
    /// target classical bit
    Meas(Addr, Addr),
    /// IO out
    Out(Box<IoOutGate>),
}

impl CGate {
    pub fn qbits(&self) -> &[Addr] {
        if let CGate::Control(_, qg) = self {
            qg.qbits()
        } else {
            &[]
        }
    }

    pub fn cbits(&self) -> &[Addr] {
        use CGate::*;
        // NOTE: A ridiculous unsafe optimization that almost certainly yields no
        // measurable performance benefits, and will lead to a bug as soon as I
        // forget about it and change the data layout of `CGate`. This is
        // basically bad engineering in the name of fun.
        use std::mem::Discriminant;
        let tgts = match self {
            CGate::Not(_) => 1,
            CGate::Copy(_, _) => 2,
            CGate::Cnot(_, _) => 2,
            CGate::Control(_, _) => 1,
        };
        // Safety: `CGate` is `#[repr(C)]`
        unsafe {
            let ptr = (self as *const Self as *const Discriminant<Self>).add(1);
            std::slice::from_raw_parts(ptr as *const Addr, tgts)
        }
    }
}

impl QGate {
    pub fn qbits(&self) -> &[Addr] {
        use QGate::*;
        // NOTE: A ridiculous unsafe optimization that almost certainly yields no
        // measurable performance benefits, and will lead to a bug as soon as I
        // forget about it and change the data layout of `QGate`. This is
        // basically bad engineering in the name of fun.
        use std::mem::Discriminant;
        let tgts = match self {
            X(_) => 1,
            T { .. } => 1,
            H(_) => 1,
            Z(_) => 1,
            CX { .. } => 2,
            SWAP { .. } => 2,
        };
        // Safety: `QGate` is `#[repr(C)]`
        unsafe {
            let ptr = (self as *const Self as *const Discriminant<Self>).add(1);
            std::slice::from_raw_parts(ptr as *const Addr, tgts)
        }
    }

    pub fn conjugate(self) -> QGate {
        use QGate::*;
        match self {
            T { tgt, conj } => T { tgt, conj: !conj },
            _ => self,
        }
    }

    #[rustfmt::skip]
    fn controlled_on_one(self, ctrl: Addr) -> Vec<QGate> {
        use QGate::*;
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
        }
    }

    /// Control on multiple qubits
    pub fn controlled_on(self, ctrls: Box<dyn Iterator<Item = Addr>>) -> Vec<QGate> {
        let mut inner_gates = vec![self];
        for ctrl in ctrls {
            inner_gates = inner_gates
                .into_iter()
                .flat_map(|gate| gate.controlled_on_one(ctrl))
                .collect::<Vec<QGate>>()
        }
        inner_gates
    }
}

pub trait MaxBits {
    fn max_qbit(&self) -> Option<usize>;
    fn max_cbit(&self) -> Option<usize>;
}

impl MaxBits for QGate {
    fn max_qbit(&self) -> Option<usize> {
        self.qbits().iter().cloned().max()
    }

    fn max_cbit(&self) -> Option<usize> {
        None
    }
}

impl MaxBits for CGate {
    fn max_qbit(&self) -> Option<usize> {
        self.cbits().iter().cloned().max()
    }

    fn max_cbit(&self) -> Option<usize> {
        self.qbits().iter().cloned().max()
    }
}

impl MaxBits for Inst {
    fn max_qbit(&self) -> Option<usize> {
        match self {
            Inst::CInit(_) => None,
            Inst::CFree(_) => None,
            Inst::QInit(u) => Some(*u),
            Inst::QFree(u) => Some(*u),
            Inst::QGate(g) => g.max_qbit(),
            Inst::CGate(g) => g.max_qbit(),
            Inst::Meas(u, _) => Some(*u),
            Inst::Out(_) => todo!(),
        }
    }

    fn max_cbit(&self) -> Option<usize> {
        match self {
            Inst::CInit(u) => Some(*u),
            Inst::CFree(u) => Some(*u),
            Inst::QInit(_) => None,
            Inst::QFree(_) => None,
            Inst::QGate(g) => g.max_cbit(),
            Inst::CGate(g) => g.max_qbit(),
            Inst::Meas(_, u) => Some(*u),
            Inst::Out(_) => todo!(),
        }
    }
}

impl From<QGate> for Inst {
    fn from(g: QGate) -> Self {
        Self::QGate(g)
    }
}

impl From<CGate> for Inst {
    fn from(g: CGate) -> Self {
        Self::CGate(g)
    }
}

impl IntoTarget<Qasm> for QGate {
    #[rustfmt::skip]
    fn into_target(self, _target: &Qasm) -> String {
        use QGate::*;
        match self {
            X(tgt)            => format!("x q[{}];", tgt),
            T { tgt, conj }   => format!("{} q[{}];",
                                         if conj { "tdg" } else { "t" },
                                         tgt),
            H(tgt)            => format!("h q[{}];", tgt),
            Z(tgt)            => format!("z q[{}];", tgt),
            CX { tgt, ctrl }  => format!("cx q[{}], q[{}];", ctrl, tgt),
            SWAP { .. }       => todo!(),
        }
    }
}

impl IntoTarget<Qasm> for Inst {
    #[rustfmt::skip]
    fn into_target(self, target: &Qasm) -> String {
        match self {
            Inst::QGate(g)    => g.into_target(target),
            Inst::Meas(src, tgt) => format!("measure q[{}] -> c[{}]", src, tgt),
            Inst::Out(io)      => {
                // TODO OpenQASM doesn't support this kind of operation, does it? What
                // should we do here?
                format!("// copy c[{}] __out_{}[{}] ", io.addr, io.name, io.elem)
            },
            _ => String::new(),
        }
    }
}

/// A simple circuit struct. This backend data structure keeps changing, but it
#[derive(Debug)]
pub struct CircuitBuf {
    insts: Vec<Inst>,
    max_qbit: Option<usize>,
    max_cbit: Option<usize>,
}

impl CircuitBuf {
    pub fn new() -> Self {
        Self {
            insts: Vec::new(),
            max_qbit: None,
            max_cbit: None,
        }
    }

    pub fn qbit_size(&self) -> usize {
        match self.max_qbit {
            Some(n) => n + 1,
            None => 0,
        }
    }

    pub fn cbit_size(&self) -> usize {
        match self.max_cbit {
            Some(n) => n + 1,
            None => 0,
        }
    }

    pub fn into_iter(self) -> CircuitStream {
        CircuitStream {
            gates: self.insts.into_iter(),
        }
    }

    pub fn push<T>(&mut self, g: T)
    where
        T: Into<Inst> + MaxBits,
    {
        self.max_qbit = self.max_qbit.max(g.max_qbit());
        self.max_cbit = self.max_qbit.max(g.max_cbit());
        self.insts.push(g.into());
    }
}

pub struct CircuitStream {
    gates: IntoIter<Inst>,
}

impl Iterator for CircuitStream {
    type Item = Inst;

    fn next(&mut self) -> Option<Self::Item> {
        self.gates.next()
    }
}

// === Formatting implementations

impl std::fmt::Display for QGate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use QGate::*;
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
        }
    }
}
