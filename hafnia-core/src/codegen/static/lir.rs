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
            M(q) => M(self.qtransl(q)),
            Out(gate) => {
                let mut gate = gate.clone();
                gate.addr = self.qtransl(&gate.addr);
                Gate::Out(gate)
            }
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
