use crate::{ast::FnId, store::Index};
use crate::{
    target::{qasm::Qasm, IntoTarget, Target},
    types::TypeSize,
};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};
use Gate::*;

/// This type alias identifies qubits with their numerical indices
pub type VirtAddr = usize;

pub type PhysAddr = usize;

/// These are gates from which most ordinary circuits will be built
#[allow(clippy::upper_case_acronyms)]
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

/// An allocation of locally indexed virtual addresses
#[derive(Debug, Clone, Default)]
pub struct BitSet {
    pub qbits: Vec<VirtAddr>,
    pub cbits: Vec<VirtAddr>,
}

impl BitSet {
    pub fn new() -> Self {
        Self {
            qbits: Vec::new(),
            cbits: Vec::new(),
        }
    }

    /// Create an uninitialized set of address bindings
    pub fn uninit(sz: &TypeSize) -> Self {
        Self {
            qbits: vec![0; sz.qsize],
            cbits: vec![0; sz.csize],
        }
    }

    pub fn append(&mut self, other: &mut BitSet) {
        self.qbits.append(&mut other.qbits);
        self.cbits.append(&mut other.cbits);
    }

    // NOTE I don't think this can actually be done with the Index trait without
    // GATs.
    pub fn index<'b: 'a, 'a>(
        &'b self,
        idx: (std::ops::Range<VirtAddr>, std::ops::Range<VirtAddr>),
    ) -> BitSetSlice<'a> {
        BitSetSlice {
            qbits: &self.qbits[idx.0],
            cbits: &self.cbits[idx.1],
        }
    }

    pub fn index_mut<'b: 'a, 'a>(
        &'b mut self,
        idx: (std::ops::Range<VirtAddr>, std::ops::Range<VirtAddr>),
    ) -> BitSetSliceMut<'a> {
        BitSetSliceMut {
            qbits: &mut self.qbits[idx.0],
            cbits: &mut self.cbits[idx.1],
        }
    }
}

pub struct BitSetSlice<'a> {
    pub qbits: &'a [VirtAddr],
    pub cbits: &'a [VirtAddr],
}

impl BitSetSlice<'_> {
    // NOTE should really use the ToOwned trait
    pub fn to_owned(&self) -> BitSet {
        BitSet {
            qbits: self.qbits.to_owned(),
            cbits: self.cbits.to_owned(),
        }
    }
}

pub struct BitSetSliceMut<'a> {
    pub qbits: &'a mut [VirtAddr],
    pub cbits: &'a mut [VirtAddr],
}

/// A terrible name that will be fixed later: each of the "things" that take
/// place, namely gates and procedure calls.
#[derive(Debug)]
pub enum Instruction {
    Gate(Gate),
    FnCall(FnId, BitSet),
}

/// The type of a single procedure in the low-level circuit IR. For now, these
/// are *finite* lists of gates and procedure calls. In the future, they will
/// look more like some kind of stream.
///
/// FIXME Also, this is not a great name for this struct, and it's likely to change.
#[derive(Default, Debug)]
pub struct LirGraph {
    /// number of quantum local bits
    pub qlocals: usize,
    /// number of classical local bits
    pub clocals: usize,
    /// The local qubits that are free at the end of the procedure
    pub freed: Vec<usize>,
    /// All the instructions of the compiled subroutine. Note that this is, for
    /// now, a finite structure. That is likely to change.
    pub instructions: Vec<Instruction>,
}

/// This is the low-level IR, which is a blend of the MIR and a circuit.
#[derive(Default, Debug)]
pub struct Lir {
    pub graphs: HashMap<FnId, LirGraph>,
    pub entry_point: FnId,
}

impl Lir {
    pub fn max_qubit(&self) -> Option<usize> {
        // FIXME This is manifestly wrong. Although maybe this struct shouldn't
        // have any such idea, anyway.
        None
    }

    pub fn iter(&self) -> CircuitStream {
        CircuitStream::new(self)
    }
}

/// The qubit allocator structure that *maybe* shouldn't be a black box. But
/// this will do for now.
///
/// As a matter of fact, we should maybe use the *exact same* struct for
/// allocation within a function.
struct GlobalAllocator {
    pub qctr: std::ops::RangeFrom<usize>,
    pub cctr: std::ops::RangeFrom<usize>,
    /// Qubits that have been returned to the allocator after being zeroed-out
    /// or proven |0>.
    pub free: VecDeque<PhysAddr>,
}

impl GlobalAllocator {
    fn new() -> Self {
        Self {
            qctr: 0..,
            cctr: 0..,
            free: VecDeque::new(),
        }
    }

    fn qalloc(&mut self, n: usize) -> Vec<PhysAddr> {
        (&mut self.qctr).take(n).collect()
    }

    // Again, a terrible name, has nothing to do with C `calloc`
    fn calloc(&mut self, n: usize) -> Vec<PhysAddr> {
        (&mut self.cctr).take(n).collect()
    }
}

/// Maybe or maybe not the right name for this data structure. Holds the
/// instructions and address mapping table for the current function call.
struct StackFrame<'c> {
    insts: std::slice::Iter<'c, Instruction>,
    // TODO: [PERF] Figure out a more efficient way to handle address
    // translation *later*. No premature optimization right now.
    table: BitSet,
}

impl<'c> Iterator for StackFrame<'c> {
    type Item = &'c Instruction;

    fn next(&mut self) -> Option<Self::Item> {
        self.insts.next()
    }
}

pub struct CircuitStream<'c> {
    circ: &'c Lir,
    allocator: GlobalAllocator,
    active: StackFrame<'c>,
    // FIXME this implementation is a problem for arbitrary mutual recursion,
    // as the stack will grow indefinitely.
    stack: Vec<StackFrame<'c>>,
}

impl<'c> CircuitStream<'c> {
    fn new(circ: &'c Lir) -> Self {
        let mut allocator = GlobalAllocator::new();
        let gr = &circ.graphs[&circ.entry_point];
        let insts = gr.instructions.iter();
        let frame = StackFrame {
            insts,
            table: BitSet {
                qbits: allocator.qalloc(gr.qlocals),
                cbits: allocator.calloc(gr.clocals),
            },
        };
        Self {
            circ,
            allocator,
            active: frame,
            stack: vec![],
        }
    }

    fn push_stack_frame(&mut self, fn_id: FnId, bits: BitSet) {
        let gr = &self.circ.graphs[&fn_id];
        let insts = gr.instructions.iter();
        let mut table = bits;
        let qpriv = gr.qlocals - table.qbits.len();
        let cpriv = gr.clocals - table.cbits.len();
        table.qbits.extend((&mut self.allocator.qctr).take(qpriv));
        table.cbits.extend((&mut self.allocator.cctr).take(cpriv));
        let frame = StackFrame { insts, table };
        self.stack.push(frame);
    }

    /// Contract: there is at least one frame on the stack.
    fn pop_stack_frame(&mut self) {
        self.active = self.stack.pop().unwrap();
    }

    /// Address
    fn qtransl(&self, bit: &VirtAddr) -> PhysAddr {
        self.active.table.qbits[*bit]
    }

    /// Address translation to physical bits
    fn transl_gate(&self, gate: &Gate) -> Gate {
        match gate {
            X(q) => X(self.qtransl(q)),
            T { tgt, conj } => T {
                tgt: self.qtransl(tgt),
                conj: *conj,
            },
            H(q) => H(self.qtransl(q)),
            Z(q) => Z(self.qtransl(q)),
            CX { tgt, ctrl } => CX {
                tgt: self.qtransl(tgt),
                ctrl: self.qtransl(ctrl),
            },
            // probably shouldn't exist at this level
            SWAP { fst, snd } => SWAP {
                fst: self.qtransl(fst),
                snd: self.qtransl(snd),
            },
            M(_) => todo!(),
        }
    }
}

impl<'c> Iterator for CircuitStream<'c> {
    type Item = Gate;

    fn next(&mut self) -> Option<Self::Item> {
        match self.active.next() {
            None => {
                if self.stack.len() > 0 {
                    self.pop_stack_frame();
                    self.next()
                } else {
                    None
                }
            }
            Some(Instruction::Gate(gate)) => Some(self.transl_gate(gate)),
            Some(Instruction::FnCall(fn_id, bits)) => {
                // FIXME: [PERF] probably-unnecessary clone
                self.push_stack_frame(*fn_id, bits.clone());
                self.next()
            }
        }
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
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Gate(g) => write!(f, "{}", g),
            Instruction::FnCall(fn_id, args) => {
                write!(f, "{}(", fn_id.into_usize())?;
                // TODO cbits too
                let mut qbits = args.qbits.iter();
                if let Some(arg) = qbits.next() {
                    write!(f, "{}", arg)?;
                    for arg in qbits {
                        write!(f, ", {}", arg)?;
                    }
                }
                f.write_str(")")
            }
        }
    }
}

/// Write the body of the routine
impl std::fmt::Display for LirGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for inst in self.instructions.iter() {
            writeln!(f, "\t{};", inst)?;
        }
        Ok(())
    }
}

/// Write all the routines
impl std::fmt::Display for Lir {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (fn_id, gr) in &self.graphs {
            if *fn_id == self.entry_point {
                f.write_str("main {\n")?;
            } else {
                writeln!(f, "{} {{", fn_id.into_usize())?;
            }
            writeln!(f, "{}}}", gr)?;
        }
        Ok(())
    }
}
