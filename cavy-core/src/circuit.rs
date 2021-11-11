use crate::{ast::FnId, index_type, store::Index, util::FmtWith};
use crate::{
    context::SymbolId,
    target::{qasm::Qasm, Target},
    types::TypeSize,
};
use std::{
    cmp,
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    vec::IntoIter,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

index_type! { Qbit }
index_type! { Cbit }

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IoUse {
    /// Classical address to read from or write to
    pub addr: Cbit,
    /// Name of the ext location. Maybe this could be a `SymbolId`--but that
    /// would necessitate refactoring the `target` api, and I really don't want
    /// to go there.
    pub channel: SymbolId,
    /// Direction of the channel
    pub dir: crate::ast::IoDirection,
    /// Bit of the ext location
    pub elem: usize,
}

/// The base gates from which we will build circuits
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BaseGateQ {
    X(Qbit),
    H(Qbit),
    Z(Qbit),
    T(Qbit),
    TDag(Qbit),
    S(Qbit),
    SDag(Qbit),
    /// An arbitrary-phase gate, in units of pi, with the convention that a
    /// phase of +/- 1 is a Z gate.
    Phase(Qbit, f32),
    /// Ok, this isn't *great* in that there are *two representations* of the
    /// *same gate*. But it seems to make code generation easier. We could call
    /// it an optimization: A CX as a `GateQ` with a single control costs a heap
    /// allocation; a `GateQ` containing a a `Cnot` and no controls does not.
    Cnot {
        ctrl: Qbit,
        tgt: Qbit,
    },
    /// This might "really" belong in `GateQ`, but it makes control
    /// unrolling a bit challenging.
    Swap(Qbit, Qbit),
}

/// These are gates that might decompose into more primitive base gates.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateQ {
    pub ctrls: Vec<(Qbit, bool)>,
    pub base: BaseGateQ,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BaseGateC {
    Not(Cbit),
    /// Ibid the `BaseGateQ` `Cnot` gate
    Cnot {
        ctrl: Cbit,
        tgt: Cbit,
    },
    Swap(Cbit, Cbit),
    /// The first address is the source bit; the second is the target bit
    Copy(Cbit, Cbit),
}

/// For classical-controlled gates, the target can be either a classical or
/// quantum bit.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BaseGate {
    C(BaseGateC),
    Q(BaseGateQ),
}

impl From<BaseGateQ> for BaseGate {
    fn from(g: BaseGateQ) -> Self {
        Self::Q(g)
    }
}

impl From<BaseGateC> for BaseGate {
    fn from(g: BaseGateC) -> Self {
        Self::C(g)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateC {
    pub ctrls: Vec<(Cbit, bool)>,
    pub base: BaseGate,
}

impl From<BaseGateQ> for GateQ {
    fn from(g: BaseGateQ) -> Self {
        Self {
            ctrls: vec![],
            base: g,
        }
    }
}

impl From<BaseGateQ> for GateC {
    fn from(g: BaseGateQ) -> Self {
        Self {
            ctrls: vec![],
            base: BaseGate::Q(g),
        }
    }
}

impl From<BaseGateC> for GateC {
    fn from(g: BaseGateC) -> Self {
        Self {
            ctrls: vec![],
            base: BaseGate::C(g),
        }
    }
}

/// Is a freed bit clean (known pure state) or dirty (unknown, possibly
/// entangled [if qubit]?)
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FreeState {
    /// Known pure state
    Clean,
    /// Unknown state, (if qubit) possibly entangled
    Dirty,
}

/// The simple instructions that make up the low-level circuit stream
/// representation
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Inst {
    /// Bring up a bit rail
    CInit(Cbit),
    /// Set down a bit rail
    CFree(Cbit, FreeState),
    /// Bring up a qubit rail
    QInit(Qbit),
    /// Set down a qubit rail
    QFree(Qbit, FreeState),
    /// A quantum gate
    QGate(GateQ),
    /// A classical gate
    CGate(GateC),
    /// Measurement: the first address is the qubit measured; the second is the
    /// target classical bit
    Meas(Qbit, Cbit),
    /// IO use
    Io(Box<IoUse>),
}

impl BaseGateQ {
    pub fn conj(self) -> BaseGateQ {
        use BaseGateQ::*;
        match self {
            T(u) => TDag(u),
            TDag(u) => T(u),
            S(u) => SDag(u),
            SDag(u) => S(u),
            Phase(u, phase) => Phase(u, -phase),
            _ => self,
        }
    }

    pub fn control(self, ctrl: Qbit) -> GateQ {
        GateQ {
            ctrls: vec![(ctrl, true)],
            base: self,
        }
    }
}

impl GateQ {
    pub fn conj(mut self) -> GateQ {
        self.base = self.base.conj();
        self
    }

    pub fn is_cx(&self) -> bool {
        (matches!(self.base, BaseGateQ::X(_)) && self.ctrls.len() == 1)
            || (matches!(self.base, BaseGateQ::Cnot { .. }) && self.ctrls.is_empty())
    }

    pub fn is_cz(&self) -> bool {
        matches!(self.base, BaseGateQ::Z(_)) && self.ctrls.len() == 1
    }

    pub fn is_swap(&self) -> bool {
        matches!(self.base, BaseGateQ::Swap(_, _)) && self.ctrls.is_empty()
    }

    pub fn is_cswap(&self) -> bool {
        matches!(self.base, BaseGateQ::Swap(_, _)) && self.ctrls.len() == 1
    }

    // #[rustfmt::skip]
    // fn controlled_on_one(self, ctrl: Addr) -> Vec<QGate> {
    //     use QGate::*;
    //     match self {
    //         X(tgt) => vec![CX { ctrl, tgt }],
    //         T { tgt: _, conj: _ } => todo!(),
    //         H(_tgt) => todo!(),
    //         Z(tgt) => vec![
    //             H(tgt),
    //             CX { ctrl, tgt },
    //             H(tgt)
    //         ],
    //         // This is just applying a well-known identity for CCX.
    //         CX { ctrl: inner_ctrl, tgt } => vec![
    //             H(tgt),
    //             CX { ctrl: inner_ctrl, tgt },
    //             T { tgt, conj: true},
    //             CX { ctrl, tgt },
    //             T { tgt, conj: false },
    //             CX { ctrl: inner_ctrl, tgt },
    //             T { tgt, conj: true},
    //             CX { ctrl, tgt },
    //             T { tgt: inner_ctrl, conj: false },
    //             T { tgt, conj: false },
    //             CX { ctrl, tgt: inner_ctrl },
    //             H(tgt),
    //             T { tgt: ctrl, conj: false },
    //             T { tgt: inner_ctrl, conj: true },
    //             CX { ctrl, tgt: inner_ctrl },
    //         ],
    //         Swap{ .. } => todo!(),
    //     }
    // }

    // /// Control on multiple qubits
    // pub fn controlled_on(self, ctrls: Box<dyn Iterator<Item = Addr>>) -> Vec<QGate> {
    //     let mut inner_gates = vec![self];
    //     for ctrl in ctrls {
    //         inner_gates = inner_gates
    //             .into_iter()
    //             .flat_map(|gate| gate.controlled_on_one(ctrl))
    //             .collect::<Vec<QGate>>()
    //     }
    //     inner_gates
    // }
}

pub trait MaxBits {
    fn max_qbit(&self) -> Option<Qbit>;
    fn max_cbit(&self) -> Option<Cbit>;
}

impl MaxBits for BaseGateQ {
    fn max_qbit(&self) -> Option<Qbit> {
        let max = *match self {
            BaseGateQ::X(u) => u,
            BaseGateQ::H(u) => u,
            BaseGateQ::Z(u) => u,
            BaseGateQ::T(u) => u,
            BaseGateQ::TDag(u) => u,
            BaseGateQ::S(u) => u,
            BaseGateQ::SDag(u) => u,
            BaseGateQ::Phase(u, _) => u,
            BaseGateQ::Cnot { ctrl, tgt } => cmp::max(ctrl, tgt),
            BaseGateQ::Swap(u, v) => cmp::max(u, v),
        };
        Some(max)
    }

    fn max_cbit(&self) -> Option<Cbit> {
        None
    }
}

impl MaxBits for GateQ {
    fn max_qbit(&self) -> Option<Qbit> {
        cmp::max(
            self.ctrls.iter().map(|(u, _)| u).max().cloned(),
            self.base.max_qbit(),
        )
    }

    fn max_cbit(&self) -> Option<Cbit> {
        None
    }
}

impl MaxBits for BaseGateC {
    fn max_qbit(&self) -> Option<Qbit> {
        None
    }

    fn max_cbit(&self) -> Option<Cbit> {
        let max = *match self {
            BaseGateC::Not(u) => u,
            BaseGateC::Cnot { ctrl, tgt } => cmp::max(ctrl, tgt),
            BaseGateC::Swap(fst, snd) => cmp::max(fst, snd),
            BaseGateC::Copy(u, v) => cmp::max(u, v),
        };
        Some(max)
    }
}

impl MaxBits for BaseGate {
    fn max_qbit(&self) -> Option<Qbit> {
        match self {
            BaseGate::C(x) => x.max_qbit(),
            BaseGate::Q(x) => x.max_qbit(),
        }
    }

    fn max_cbit(&self) -> Option<Cbit> {
        match self {
            BaseGate::C(x) => x.max_cbit(),
            BaseGate::Q(x) => x.max_cbit(),
        }
    }
}

impl MaxBits for GateC {
    fn max_qbit(&self) -> Option<Qbit> {
        self.base.max_qbit()
    }

    fn max_cbit(&self) -> Option<Cbit> {
        cmp::max(
            self.ctrls.iter().map(|(u, _)| u).max().cloned(),
            self.base.max_cbit(),
        )
    }
}

// NOTE: The `Free` instructions currently evaluate to `None.` This is really a
// hack to make sure that the bit counts are all correct, even if some variables
// have been optimized away without removing their `Drop` instructions.
//
// Really, this is incorrect. First of all, that shouldn't happen during
// optimization: the fact that it does is a result of the naive way that I'm
// approaching constant propagation, which should actually be based on a live
// variable analysis.
//
// Second, I might *actually* want to insert `Drop`s *later*, not during
// lowering, because we want to free ancillas *as soon as possible*. I belive
// this is a departure from what Rust does.
impl MaxBits for Inst {
    fn max_qbit(&self) -> Option<Qbit> {
        match self {
            Inst::CInit(_) => None,
            Inst::CFree(_, _) => None,
            Inst::QInit(u) => Some(*u),
            Inst::QFree(_u, _) => None,
            Inst::QGate(g) => g.max_qbit(),
            Inst::CGate(g) => g.max_qbit(),
            Inst::Meas(u, _) => Some(*u),
            Inst::Io(_) => None,
        }
    }

    fn max_cbit(&self) -> Option<Cbit> {
        match self {
            Inst::CInit(u) => Some(*u),
            Inst::CFree(_u, _) => None,
            Inst::QInit(_) => None,
            Inst::QFree(_, _) => None,
            Inst::QGate(g) => g.max_cbit(),
            Inst::CGate(g) => g.max_cbit(),
            Inst::Meas(_, u) => Some(*u),
            Inst::Io(io) => Some(io.addr),
        }
    }
}

impl From<GateQ> for Inst {
    fn from(g: GateQ) -> Self {
        Self::QGate(g)
    }
}

impl From<GateC> for Inst {
    fn from(g: GateC) -> Self {
        Self::CGate(g)
    }
}

impl From<BaseGateQ> for Inst {
    fn from(g: BaseGateQ) -> Self {
        Self::QGate(g.into())
    }
}

impl From<BaseGateC> for Inst {
    fn from(g: BaseGateC) -> Self {
        Self::CGate(g.into())
    }
}

/// A simple circuit struct. This backend data structure keeps changing, but it
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CircuitBuf {
    insts: Vec<Inst>,
    pub max_qbit: Option<Qbit>,
    pub max_cbit: Option<Cbit>,
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
            Some(n) => Into::<u32>::into(n) as usize + 1,
            None => 0,
        }
    }

    pub fn cbit_size(&self) -> usize {
        match self.max_cbit {
            Some(n) => Into::<u32>::into(n) as usize + 1,
            None => 0,
        }
    }

    // FIXME 4
    pub fn into_iter(self) -> impl Iterator<Item = Inst> {
        self.insts.into_iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = &'_ Inst> {
        self.insts.iter()
    }

    pub fn push<T>(&mut self, g: T)
    where
        T: Into<Inst> + MaxBits,
    {
        self.max_qbit = self.max_qbit.max(g.max_qbit());
        self.max_cbit = self.max_cbit.max(g.max_cbit());
        self.insts.push(g.into());
    }
}

impl std::iter::FromIterator<Inst> for CircuitBuf {
    fn from_iter<T: IntoIterator<Item = Inst>>(iter: T) -> Self {
        let mut circ = Self::new();
        for inst in iter {
            circ.push(inst);
        }
        circ
    }
}

impl From<Vec<Inst>> for CircuitBuf {
    fn from(insts: Vec<Inst>) -> Self {
        let (max_qbit, max_cbit) = insts.iter().fold((None, None), |(q, c), inst| {
            (cmp::max(q, inst.max_qbit()), cmp::max(c, inst.max_cbit()))
        });
        Self {
            max_qbit,
            max_cbit,
            insts,
        }
    }
}

// === Implementations ===

impl std::fmt::Display for BaseGateQ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BaseGateQ::*;
        match self {
            X(q) => write!(f, "X {}", q),
            H(q) => write!(f, "H {}", q),
            Z(q) => write!(f, "Z {}", q),
            T(q) => write!(f, "T {}", q),
            TDag(q) => write!(f, "T* {}", q),
            S(q) => write!(f, "S {}", q),
            SDag(q) => write!(f, "S* {}", q),
            Phase(q, phase) => write!(f, "@ {} {}", phase, q),
            Cnot { ctrl, tgt } => write!(f, "CNOT {} {}", ctrl, tgt),
            Swap(fst, snd) => write!(f, "SWAP {} {}", fst, snd),
        }
    }
}

impl std::fmt::Display for Qbit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Cbit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
