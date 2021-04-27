//! In this module we outline the backend APIs for various target languages.
//! This is all pretty unstable for the time being, so don’t rely on it too much
//! externally.

use crate::circuit::CircuitBuf;

/// This type alias replaces the associated type previously attached to `Target`
pub type ObjectCode = String;

/// This is a marker trait for compile targets. Must be `Send` in order to use
/// `Box<dyn Target>` in FFI.
pub trait Target: std::fmt::Debug + Send {
    fn from(&self, circ: CircuitBuf) -> ObjectCode;
}

impl Default for Box<dyn Target> {
    fn default() -> Self {
        Box::new(null::NullTarget())
    }
}

/// This trait is implemented by internal structs which, during code
/// generation, need inform the target safely about their private fields.
pub trait IntoTarget<T>
where
    T: Target,
{
    fn into_target(self, target: &T) -> ObjectCode;
}

/// A null target for testing and running partial compiler pipelines.
pub mod null {
    use super::*;

    #[derive(Debug)]
    pub struct NullTarget();
    impl Target for NullTarget {
        fn from(&self, _circ: CircuitBuf) -> ObjectCode {
            String::new()
        }
    }
}

/// OpenQASM target, the default "assembly" backend most useful for interop with
/// scripting language tools.
pub mod qasm {
    use super::*;

    /// There is a version 3 of QASM, but we’re only going to use 2.0 for now, since
    /// this is what Cirq supports.
    pub const QASM_VERSION: &str = "2.0";

    /// The Qasm object code type is just a wrapper around a String.
    #[derive(Debug)]
    pub struct Qasm;

    impl Qasm {
        fn headers(&self) -> String {
            format!("OPENQASM {};\ninclude \"qelib1.inc\";", QASM_VERSION)
        }

        fn circuit(&self, circuit: crate::circuit::CircuitBuf) -> String {
            circuit.into_target(self)
        }
    }

    impl Target for Qasm {
        fn from(&self, circ: CircuitBuf) -> String {
            format!("{}\n{}", self.headers(), self.circuit(circ))
        }
    }

    impl IntoTarget<Qasm> for crate::circuit::CircuitBuf {
        fn into_target(self, target: &Qasm) -> String {
            let declaration = {
                format!(
                    "qreg q[{}];\ncreg c[{}];",
                    self.qbit_size(),
                    self.cbit_size()
                )
            };
            let gates = self
                .into_iter()
                .map(|gate| gate.into_target(target))
                .collect::<Vec<String>>()
                .join("\n");
            format!("{}\n{}\n", declaration, gates)
        }
    }
}

/// The LaTeX backend, which uses quantikz.
pub mod latex {
    use std::{
        fmt,
        ops::{Index, IndexMut, RangeInclusive},
    };

    use crate::circuit::{self, CGate, Inst, QGate};

    use super::*;

    // TODO the public interface and private implementation are a bit mixed
    // here: there is some functionality in the `diagram` function of `Latex`
    // that should probably go in the `new` constructor of `LayoutArray`.

    /// This backend emits a circuit in quantikz format
    #[derive(Debug)]
    pub struct Latex {
        /// Include preamble and `\begin{document}...\end{document}`?
        pub standalone: bool,
    }

    impl Latex {
        /// Escapes a string by replacing underscores with `\_`
        fn escape(s: &str) -> String {
            str::replace(s, "_", r"\_")
        }
    }

    /// Whether or not a wire has a live bit on it. Note that *might* one day
    /// want to be able to transform qubit wires into cbit wires for a more
    /// visually appealing layout, so *each cell* has the possibility of `LiveQ`
    /// or `LiveC`.
    #[derive(Debug, Clone, Copy)]
    enum Liveness {
        // A live quantum wire
        LiveQ,
        // A live classical wire
        LiveC,
        // A dead wire
        Dead,
    }

    // Let's just bring this into module scope; nothing will conflict with it.
    use Liveness::*;

    /// The three cell states in a common quantum circuit: in `Occupied(T)`, the
    /// cell is occupied by a circuit elemen. In `Free`, there is no gate or
    /// blocking element, and the wire may be live or dead. In `Blocked` there
    /// is no gate, but the cell is obstructed, as by a vertical wire, and the
    /// wire may be live or dead.
    #[derive(Debug)]
    enum LayoutState<T> {
        Occupied(T),
        Free(Liveness),
        Blocked(Liveness),
    }

    // And let's bring this into module scope, too.
    use LayoutState::*;

    /// The kinds of elements that will occupy our circuit
    #[derive(Debug)]
    #[rustfmt::skip]
    enum Elem {
        // Quantum gates
        X, Z, H, T, TDag,
        // A control label with a distance to its target
        Ctrl(isize),
        // A control target
        Targ,
        // A meter with an optional distance to its target
        Meter(Option<isize>),
        // A label for IO data
        IoLabel(Box<IoLabelData>),
    }

    #[derive(Debug)]
    struct IoLabelData {
        /// The name of the IO object being written to
        name: String,
        /// The index within the IO object being output to
        elem: usize,
    }

    impl fmt::Display for Elem {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            use Elem::*;
            match self {
                X => f.write_str(r"\gate{X}"),
                Z => f.write_str(r"\gate{Z}"),
                H => f.write_str(r"\gate{H}"),
                T => f.write_str(r"\gate{T}"),
                TDag => f.write_str(r"\gate{T^\dag}"),
                Ctrl(dist) => write!(f, r"\ctrl{{{}}}", dist),
                Targ => f.write_str(r"\targ{}"),
                Meter(targ) => {
                    f.write_str(r"\meter{}")?;
                    if let Some(dist) = targ {
                        write!(f, r" \vcw{{{}}}", dist)?;
                    }
                    Ok(())
                }
                IoLabel(io) => write!(f, "\\push{{ \\tt {}[{}] }}", io.name, io.elem),
            }
        }
    }

    /// The circuit, as we build it, will be composed of a vector of `Wire`s
    struct Wire {
        cells: Vec<LayoutState<Elem>>,
        /// On each wire, the index of the first `Free` cell, of which there is
        /// guaranteed to be at least one.
        first_free: usize,
        /// The current liveness state, for new cells
        liveness: Liveness,
    }

    impl Wire {
        fn new() -> Self {
            Self {
                cells: vec![Blocked(Dead), Free(Dead)],
                first_free: 1,
                liveness: LiveQ,
            }
        }

        fn len(&self) -> usize {
            self.cells.len()
        }
    }

    impl Index<usize> for Wire {
        type Output = LayoutState<Elem>;

        fn index(&self, index: usize) -> &Self::Output {
            &self.cells[index]
        }
    }

    impl IndexMut<usize> for Wire {
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            &mut self.cells[index]
        }
    }

    /// A private struct used by the Latex backend to lay out the circuit
    /// representation. The index order is space-major, because this should have
    /// better locality of reference, and easier to serialize without an extra
    /// allocation.
    struct LayoutArray<'l> {
        /// The target spec
        latex: &'l Latex,
        /// The wire array itself
        wires: Vec<Wire>,
        /// The index of the first classical wire
        fst_cwire: usize,
        // NOTE: Might want an auxiliary data structure to track blocked columns
    }

    impl<'l> LayoutArray<'l> {
        /// It only makes sense to construct a LaTeX circuit from a finite
        /// circuit of known size.
        fn new(latex: &'l Latex, qwires: usize, cwires: usize) -> Self {
            // Start with length at least one. It will be an invariant of this
            // data structure that there is always an empty final moment. This
            // final moment will provide the terminal $\qw$ on each wire.
            //
            // (In fact, as a convenience we'll include *two* empty moments. The
            // first of these will be the initial $\qw$ on each wire.)
            //
            // It is also an invariant that there's at least one wire, that
            // should be enforced by `new`, although it isn't yet in a *natural* way.
            debug_assert!(qwires + cwires > 0);
            let wires = std::iter::repeat_with(|| Wire::new())
                .take(qwires + cwires)
                .collect();
            Self {
                latex,
                wires,
                fst_cwire: qwires,
            }
        }

        // NOTE: Is it really necessary to maintain the invariant that all the
        // wires are the same length at all times? We do extra work checking for
        // empty moments on wires.
        fn add_moment(&mut self) {
            for wire in self.wires.iter_mut() {
                wire.cells.push(Free(wire.liveness));
            }
        }

        fn len(&self) -> usize {
            self.wires[0].len()
        }

        fn width(&self) -> usize {
            self.wires.len()
        }

        /// Translate from qwire address to absolute address
        #[inline(always)]
        fn qwire(&self, wire: usize) -> usize {
            wire
        }

        /// Translate from cwire address to absolute address
        #[inline(always)]
        fn cwire(&self, wire: usize) -> usize {
            wire + self.fst_cwire
        }

        /// How quantikz expects distances to be calculated. Here, `src` denotes
        /// e.g. the source of a control operation; `tgt` denotes its target.
        #[inline(always)]
        fn dist(src: usize, tgt: usize) -> isize {
            (tgt as isize) - (src as isize)
        }

        fn push_inst(&mut self, inst: circuit::Inst) {
            match inst {
                Inst::CInit(_) => {}
                Inst::CFree(_) => {}
                Inst::QInit(_) => {}
                Inst::QFree(_) => {}
                Inst::QGate(g) => self.push_qgate(g),
                Inst::CGate(g) => self.push_cgate(g),
                Inst::Meas(s, t) => self.push_meas(self.qwire(s), self.cwire(t)),
                Inst::Out(io) => self.push_io_out(&io),
            }
        }

        fn push_qgate(&mut self, gate: QGate) {
            use QGate::*;
            let (wire, elem) = match gate {
                X(u) => (u, Elem::X),
                T { tgt, conj } => {
                    if conj {
                        (tgt, Elem::TDag)
                    } else {
                        (tgt, Elem::T)
                    }
                }
                H(u) => (u, Elem::H),
                Z(u) => (u, Elem::Z),
                CX { ctrl, tgt } => {
                    let dist = Self::dist(ctrl, tgt);
                    let ctrl = (ctrl, Elem::Ctrl(dist));
                    let tgt = (tgt, Elem::Targ);
                    self.insert_multiple(vec![ctrl, tgt]);
                    return;
                }
                SWAP { .. } => todo!(),
            };
            let wire = self.qwire(wire);
            self.wires[wire].liveness = LiveQ;
            self.insert_single(wire, elem);
        }

        fn push_cgate(&mut self, gate: CGate) {
            use CGate::*;
            let (wire, elem) = match gate {
                Not(u) => (u, Elem::Targ),
                Copy(_, _) => todo!(),
                Cnot(_, _) => todo!(),
                Control(_, _) => todo!(),
            };
            let wire = self.cwire(wire);
            self.wires[wire].liveness = LiveC;
            self.insert_single(wire, elem);
        }

        fn push_meas(&mut self, src: usize, tgt: usize) {
            let dist = Self::dist(src, tgt);
            self.wires[tgt].liveness = LiveC;
            self.wires[src].liveness = Dead;
            let src = (src, Elem::Meter(Some(dist)));
            let tgt = (tgt, Elem::Targ);
            self.insert_multiple(vec![src, tgt])
        }

        fn push_io_out(&mut self, _io: &circuit::IoOutGate) {
            todo!()
        }

        fn insert_single(&mut self, wire: usize, elem: Elem) {
            let arr_len = self.len(); // compute first for borrowck
            let wire = &mut self.wires[wire];
            let mut moment = wire.first_free;
            wire[moment] = LayoutState::Occupied(elem);

            while moment < arr_len - 1 {
                moment += 1;
                if let Free(_) = wire[moment] {
                    wire.first_free = moment;
                    return;
                }
            }

            // There are no empty cells on this wire!
            wire.first_free = arr_len;
            self.add_moment();
        }

        /// Returns true if and only if the range of wires between `lower` and
        /// `upper` (inclusive!) is all free.
        fn range_free(&self, moment: usize, range: RangeInclusive<usize>) -> bool {
            self.wires[range]
                .iter()
                .all(|wire| matches!(wire[moment], Free(_)))
        }

        fn insert_multiple(&mut self, elems: Vec<(usize, Elem)>) {
            // FIXME This method is pretty unweildy and inelegant. It still
            // doesn't always find the optimal layout, and its asymptotic isn't
            // great. There's probably a lovely dynamic programming algorithm
            // that fixes everything.

            // NOTE: is there a single iterator
            // adapter in the standard library for getting both the min and max
            // in one go?
            let min = *elems.iter().map(|(wire, _)| wire).min().unwrap();
            let max = *elems.iter().map(|(wire, _)| wire).max().unwrap();

            // If the last moment isn't free, we’ll have to add another one.
            let moment = if !self.range_free(self.len() - 1, min..=max) {
                self.add_moment();
                self.len() - 1
            } else {
                // Now we'll do the second-most-naive thing after always inserting
                // in the last moment: We'll start at the last moment, then walk
                // backwards until the last moment in which the gate fits, like a
                // Tetris game. It would be slightly better still to step *over*
                // intermediate gates. Note that this makes the whole layout
                // algorithm something like O(depth^2 * width), which is horrible.
                let mut moment = self.len() - 1;
                while self.range_free(moment - 1, min..=max) {
                    moment -= 1;
                }
                moment
            };
            // Now, if we're *still* at the end we need to add a new moment.
            if moment == self.len() - 1 {
                self.add_moment()
            }

            for (wire, elem) in elems.into_iter() {
                let wire = &mut self.wires[wire];
                wire[moment] = Occupied(elem);
                wire.first_free = moment + 1;
            }

            // We'll also do this suboptimally: we'll do a second pass
            // through the range, changing everything still free into Blocked.
            // We *could* do this in a single pass if we sorted `gates`. Note
            // that the range is *ex*clusive, because we can’t have the
            // ends of a CNOT being free.
            for wire in (min + 1)..max {
                let wire = &mut self.wires[wire];
                if let Free(ln) = wire[moment] {
                    wire[moment] = Blocked(ln);
                    if wire.first_free == moment {
                        wire.first_free += 1;
                    }
                }
            }
        }
    }

    impl fmt::Display for LayoutState<Elem> {
        #[rustfmt::skip]
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Occupied(elem) => write!(f, "{}", elem),
                Free(Dead)  | Blocked(Dead)  => f.write_str(" "),
                Free(LiveQ) | Blocked(LiveQ) => f.write_str(r"\qw"),
                Free(LiveC) | Blocked(LiveC) => f.write_str(r"\cw"),
            }
        }
    }

    // let cells = self.cells.iter();
    // if let Some(elem) = cells.next() {
    //     write!(f, "{}", cells.next())?;
    // }
    // for cell in cells {
    //     write!(f, "& {}", cell)?;
    // }
    // Ok(())
    impl fmt::Display for Wire {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if let Some((last, head)) = &self.cells.split_last() {
                for cell in head.iter() {
                    // Prev comment: "must not be a raw string"; why?
                    write!(f, "{} & ", cell)?;
                }
                write!(f, "{} ", last)?;
            }
            Ok(())
        }
    }

    impl fmt::Display for LayoutArray<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.latex.standalone {
                writeln!(f, "{}", Latex::HEADER)?;
            }
            writeln!(f, "{}", Latex::BEGIN_ENV)?;
            if let Some((last, head)) = &self.wires.split_last() {
                for wire in head.iter() {
                    writeln!(f, "{}\\\\", wire)?;
                }
                writeln!(f, "{}", last)?;
            }
            writeln!(f, "{}", Latex::END_ENV)?;
            if self.latex.standalone {
                writeln!(f, "{}", Latex::FOOTER)?;
            }
            Ok(())
        }
    }

    impl IntoTarget<Latex> for LayoutArray<'_> {
        fn into_target(self, _target: &Latex) -> String {
            format!("{}", self)
        }
    }

    impl Latex {
        const HEADER: &'static str = r"\documentclass{standalone}
\usepackage{tikz}
\usetikzlibrary{quantikz}
\usepackage[T1]{fontenc}
\begin{document}";

        const FOOTER: &'static str = r"\end{document}";

        const BEGIN_ENV: &'static str = r"\begin{quantikz}";

        const END_ENV: &'static str = r"\end{quantikz}";
    }

    impl Target for Latex {
        #[rustfmt::skip]
        fn from(&self, circ: CircuitBuf) -> ObjectCode {
            let qbits = circ.qbit_size();
            let cbits = circ.cbit_size();
            let mut layout_array = LayoutArray::new(self, qbits, cbits);

            for inst in circ.into_iter() {
                layout_array.push_inst(inst);
            }

            layout_array.into_target(self)
        }
    }
}
