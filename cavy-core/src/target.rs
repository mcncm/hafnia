//! In this module we outline the backend APIs for various target languages.
//! This is all pretty unstable for the time being, so don’t rely on it too much
//! externally.

use crate::{circuit::CircuitBuf, util::FmtWith};

/// This type alias replaces the associated type previously attached to `Target`
pub type ObjectCode = String;

/// This is a marker trait for compile targets. Must be `Send` in order to use
/// `Box<dyn Target>` in FFI.
pub trait Target: std::fmt::Debug + Send {
    fn from(&self, circ: CircuitBuf) -> ObjectCode;
}

impl<T> Target for T
where
    CircuitBuf: FmtWith<T>,
    T: std::fmt::Debug + Send,
{
    fn from(&self, circ: CircuitBuf) -> ObjectCode {
        format!("{}", circ.fmt_with(self))
    }
}

impl Default for Box<dyn Target> {
    fn default() -> Self {
        Box::new(null::NullTarget())
    }
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

#[cfg(feature = "summary")]
pub mod summary {
    use crate::circuit::{CGate, FreeState, Inst, QGate};
    use serde_json::json;

    use super::*;

    macro_rules! zero {
        ($($name:ident)*) => { $(let mut $name = 0;)* }
    }

    #[derive(Debug)]
    pub struct Summary();
    impl Target for Summary {
        fn from(&self, circ: CircuitBuf) -> ObjectCode {
            let qbits = circ.qbit_size();
            let cbits = circ.cbit_size();

            zero! {
                xgates tgates hgates zgates cxgates swapgates
                clean_frees dirty_frees
            };

            for inst in circ.into_iter() {
                match inst {
                    Inst::CInit(_) => {}
                    Inst::CFree(_, _) => {}
                    Inst::QInit(_) => {}
                    Inst::QFree(_, state) => match state {
                        FreeState::Clean => clean_frees += 1,
                        FreeState::Dirty => dirty_frees += 1,
                    },
                    Inst::QGate(g) => match g {
                        QGate::X(_) => xgates += 1,
                        QGate::T { .. } => tgates += 1,
                        QGate::H(_) => hgates += 1,
                        QGate::Z(_) => zgates += 1,
                        QGate::CX { .. } => cxgates += 1,
                        QGate::SWAP(_, _) => swapgates += 1,
                    },
                    Inst::CGate(_) => {}
                    Inst::Meas(_, _) => {}
                    Inst::Out(_) => {}
                }
            }

            let single_qubit_gates = xgates + tgates + hgates + zgates;
            let two_qubit_gates = cxgates + swapgates;
            let total_gates = single_qubit_gates + two_qubit_gates;

            let stats = json!({
                "bits": {
                    "qbits": qbits,
                    "cbits": cbits,
                    "total": qbits + cbits,
                },
                "gates": {
                    "X": xgates,
                    "T": tgates,
                    "H": hgates,
                    "Z": zgates,
                    "CX": cxgates,
                    "SWAP": swapgates,
                    "single-qubit": single_qubit_gates,
                    "two-qubit": two_qubit_gates,
                    "total": total_gates,
                },
                "frees": {
                    "clean": clean_frees,
                    "dirty": dirty_frees,
                    "total": clean_frees + dirty_frees,
                }
            });
            format!("{}", serde_json::to_string_pretty(&stats).unwrap())
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
    }

    impl FmtWith<Qasm> for CircuitBuf {
        // It's too bad that this doesn't consume the circuit. I should find a
        // way to do that, by calling `circ.into_iter()` instead of implementing
        // `FmtWith<Qasm>` for CircuitBuf. Plus, the headers logically "belong
        // to" the target data, not the circuit. The problem is that, there's no
        // way to format the iterator, because `.next()` mutates it.
        fn fmt(&self, qasm: &Qasm, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            writeln!(f, "{}", qasm.headers())?;
            writeln!(f, "qreg q[{}];", self.qbit_size())?;
            writeln!(f, "creg c[{}];", self.cbit_size())?;
            for inst in self.iter() {
                writeln!(f, "{}", inst.fmt_with(qasm))?;
            }
            Ok(())
        }
    }
}

/// The LaTeX backend, which uses quantikz.
pub mod latex {
    use std::{
        fmt, iter,
        ops::{Index, IndexMut, RangeInclusive},
    };

    use crate::circuit::{self, CGate, Inst, QGate};

    use super::*;

    /// This backend emits a circuit in quantikz format
    #[derive(Debug)]
    pub struct LaTeX {
        /// Include preamble and `\begin{document}...\end{document}`?
        pub standalone: bool,
        /// Instead of writing initial `X` gates, write the nominal input state
        pub initial_kets: bool,
    }

    impl LaTeX {
        /// Escapes a string by replacing underscores with `\_`
        fn escape(s: &str) -> String {
            str::replace(s, "_", r"\_")
        }
    }

    // == Range queries ==

    /// An inclusive interval
    struct Interval<K: Ord, V> {
        low: K,
        high: K,
        data: V,
    }

    impl<K: Ord, V> Interval<K, V> {
        fn contains(&self, k: &K) -> bool {
            k >= &self.low && k <= &self.high
        }

        fn overlaps(&self, other: &RangeInclusive<K>) -> bool {
            self.contains(other.start()) || self.contains(other.end())
        }
    }

    // FIXME: This implementation does the naive O(n) things, which means our
    // insertions will become O(n^2). If that starts to become a problem, you
    // should use a proper interval tree.
    /// Insert and query intervals with inclusive endpoints. Queries return
    /// sorted, unique values.
    struct IntervalMap<K: Ord + Copy, V: Ord + Copy> {
        intervals: Vec<Interval<K, V>>,
    }

    impl<K: Ord + Copy, V: Ord + Copy> IntervalMap<K, V> {
        fn new() -> Self {
            Self {
                intervals: Vec::new(),
            }
        }

        fn insert(&mut self, range: RangeInclusive<K>, v: V) {
            let (low, high) = (*range.start(), *range.end());
            let interval = Interval { low, high, data: v };
            self.intervals.push(interval);
        }

        fn get_by<F>(&self, f: F) -> Vec<V>
        where
            F: Fn(&&Interval<K, V>) -> bool,
        {
            let mut intervals: Vec<_> = self
                .intervals
                .iter()
                .filter(f)
                .map(|int| int.data)
                .collect();
            intervals.sort();
            intervals.dedup();
            intervals
        }

        /// Get all the values at which a key overlaps
        fn get_contained(&self, k: &K) -> Vec<V> {
            self.get_by(|int| int.contains(k))
        }

        fn get_overlaps(&self, k: RangeInclusive<K>) -> Vec<V> {
            self.get_by(|int| int.overlaps(&k))
        }
    }

    // == Layout arrays ==

    /// Whether or not a wire has a live bit on it. Note that *might* one day
    /// want to be able to transform qubit wires into cbit wires for a more
    /// visually appealing layout, so *each cell* has the possibility of `LiveQ`
    /// or `LiveC`.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    #[derive(Debug, Clone)]
    enum LayoutState<T> {
        Occupied(T),
        Free(Liveness),
    }

    // And let's bring this into module scope, too.
    use LayoutState::*;

    /// The kinds of elements that will occupy our circuit
    #[derive(Debug, Clone)]
    #[rustfmt::skip]
    enum Elem {
        // Ket state vectors
        Ket(&'static str),
        // Quantum gates
        X, Z, H, T, TDag,
        // A control label with a distance to its target
        Ctrl(isize),
        // A swap label with a distance to its target
        Swap(isize),
        // A control target
        Targ,
        // A swap target
        TargX,
        // A meter with an optional distance to its target
        Meter(Option<isize>),
        // A label for IO data
        IoLabel(Box<IoLabelData>),
    }

    #[derive(Debug, Clone)]
    struct IoLabelData {
        /// The name of the IO object being written to
        name: String,
        /// The index within the IO object being output to
        elem: usize,
    }

    impl FmtWith<LaTeX> for Elem {
        fn fmt(&self, _data: &LaTeX, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            use Elem::*;
            match self {
                Ket(s) => write!(f, "\\lstick{{$\\ket{{{}}}$}}", s),
                X => f.write_str(r"\gate{X}"),
                Z => f.write_str(r"\gate{Z}"),
                H => f.write_str(r"\gate{H}"),
                T => f.write_str(r"\gate{T}"),
                TDag => f.write_str(r"\gate{T^\dag}"),
                Ctrl(dist) => write!(f, r"\ctrl{{{}}}", dist),
                Targ => f.write_str(r"\targ{}"),
                Swap(dist) => write!(f, r"\swap{{{}}}", dist),
                TargX => f.write_str(r"\targX{}"),
                Meter(targ) => {
                    f.write_str(r"\meter{}")?;
                    if let Some(dist) = targ {
                        write!(f, r" \vcw{{{}}}", dist)?;
                    }
                    Ok(())
                }
                IoLabel(io) => write!(f, "\\push{{\\tt \\enspace {} [{}] }}", io.name, io.elem),
            }
        }
    }

    /// The circuit, as we build it, will be composed of a vector of `Wire`s
    struct Wire {
        pub cells: Vec<LayoutState<Elem>>,
        /// The sorted moments on this wire that are blocked by some vertical
        /// element
        blocked: Vec<usize>,
        /// The next free cell, computed from the `blocked` list
        next_free: usize,
        /// The first subsequent *blocked* cell, if there is one.
        next_blocked: Option<usize>,
        /// Is the list of blocked moments acceptable for use?
        blocked_valid: bool,
        /// The current liveness state, for new cells
        pub liveness: Liveness,
    }

    impl Wire {
        pub fn new() -> Self {
            Self {
                cells: vec![Free(Dead)],
                blocked: Vec::new(),
                next_free: 1,
                next_blocked: None,
                blocked_valid: true,
                liveness: Dead,
            }
        }

        pub fn len(&self) -> usize {
            self.cells.len()
        }

        fn set_blocked(&mut self, blocked: Vec<usize>) {
            debug_assert!(!self.blocked_valid);
            self.blocked = blocked;
            self.blocked_valid = true;
            self.compute_next_free();
        }

        /// Extend the wire to the given length with empty cells
        pub fn extend_to(&mut self, length: usize) {
            let diff = length.saturating_sub(self.len());
            self.cells
                .extend(iter::repeat(Free(self.liveness)).take(diff));
        }

        /// Compute and set the `next_free` field. This should be considered a private function.
        fn compute_next_free(&mut self) {
            debug_assert!(self.blocked_valid);
            let idx = match self.blocked.binary_search(&self.len()) {
                // If len is blocked, must to search ahead from the blocked
                // index.
                Ok(idx) => {
                    if idx == self.blocked.len() {
                        self.next_free = self.len() + 1;
                        self.next_blocked = None;
                    }
                    idx
                }
                // If the current length isn't a blocked index, I can just push to the array.
                Err(idx) => {
                    self.next_free = self.len();
                    self.next_blocked = self.blocked.get(idx).cloned();
                    return;
                }
            };
            // At least two elements in `self.blocked`
            for window in self.blocked[idx..].windows(2) {
                let window_len = window[1] - window[0];
                if window_len > 1 {
                    self.next_blocked = Some(window[1]);
                    self.next_free = window[0] + 1;
                    return;
                }
            }
            // Final case: no gaps between the blockages. Can unwrap because if
            // `self.blocked` were empty, would have returned len.
            self.next_free = self.blocked.last().unwrap() + 1;
            self.next_blocked = None;
        }

        pub fn invalidate_blocked(&mut self) {
            self.blocked_valid = false;
        }

        /// The blocked state might not be valid at the time we push, but it
        /// also doesn't have access to the blocked intervals list. So, we pass
        /// in a closure to allow it to retrieve them.
        pub fn push<F>(&mut self, cell: Elem, f: F)
        where
            F: Fn() -> Vec<usize>,
        {
            if !self.blocked_valid {
                self.set_blocked(f());
            }
            debug_assert!(self.blocked_valid);

            self.extend_to(self.next_free);
            self.cells.push(Occupied(cell));
        }

        /// This name is just a warning
        pub fn unchecked_push(&mut self, cell: Elem) {
            self.cells.push(Occupied(cell));
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
        /// The target spec: this *should* actually be visible during
        /// construction of the array, because we might want to add *other*
        /// LaTeX circuit libraries like qcircuit. If they have different
        /// features, this might affect the layout process itself, not just the
        /// string representation of gates.
        latex: &'l LaTeX,
        /// The wire array itself
        wires: Vec<Wire>,
        /// Blocked intervals of the array
        blocked: IntervalMap<usize, usize>,
        /// The index of the first classical wire
        fst_cwire: usize,
        // NOTE: Might want an auxiliary data structure to track blocked columns
    }

    impl<'l> LayoutArray<'l> {
        /// It only makes sense to construct a LaTeX circuit from a finite
        /// circuit of known size.
        fn new(latex: &'l LaTeX, qwires: usize, cwires: usize) -> Self {
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
            let wires = iter::repeat_with(|| Wire::new())
                .take(qwires + cwires)
                .collect();
            Self {
                latex,
                wires,
                blocked: IntervalMap::new(),
                fst_cwire: qwires,
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

        fn block_interval(&mut self, range: RangeInclusive<usize>, moment: usize) {
            self.blocked.insert(range.clone(), moment);
            for wire in range {
                self.wires[wire].invalidate_blocked();
            }
        }

        fn push_inst(&mut self, inst: circuit::Inst) {
            match inst {
                Inst::CInit(_) => {}
                Inst::CFree(_, _) => {}
                Inst::QInit(_) => {}
                Inst::QFree(_, _) => {}
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
                SWAP(u, v) => {
                    let dist = Self::dist(u, v);
                    let fst = (u, Elem::Swap(dist));
                    let snd = (v, Elem::TargX);
                    self.insert_multiple(vec![fst, snd]);
                    return;
                }
            };

            let wire_idx = self.qwire(wire);
            let wire = &mut self.wires[wire];

            let prev = wire.next_free - 1;
            if self.latex.initial_kets && wire.liveness == Dead {
                if let Elem::X = elem {
                    // NOTE: Does this violate any important invariants? Could
                    // the previous wire be blocked?
                    wire[prev] = Occupied(Elem::Ket("1"));
                    wire.liveness = LiveQ;
                    return;
                } else {
                    wire[prev] = Occupied(Elem::Ket("0"));
                }
            }
            wire.liveness = LiveQ;
            self.insert_single(wire_idx, elem);
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
            let src_pair = (src, Elem::Meter(Some(dist)));
            let tgt_pair = (tgt, Elem::Targ);
            self.insert_multiple(vec![src_pair, tgt_pair]);
            self.wires[tgt].liveness = LiveC;
            self.wires[src].liveness = Dead;
        }

        fn push_io_out(&mut self, io: &circuit::IoOutGate) {
            let wire = self.cwire(io.addr);
            let io = IoLabelData {
                // Nice, I get to clone it *again*! (See `dynamic/gates.rs`)
                name: io.name.clone(),
                elem: io.elem,
            };
            let elem = Elem::IoLabel(Box::new(io));
            self.insert_single(wire, elem);
        }

        fn insert_single(&mut self, wire: usize, elem: Elem) {
            let blocked = &self.blocked;
            self.wires[wire].push(elem, || blocked.get_contained(&wire));
        }

        /// Note that, unlike `insert_single`, the "free slots" aren't
        /// effectively cached for multiple-wire gates. This could get slow.
        fn insert_multiple(&mut self, mut elems: Vec<(usize, Elem)>) {
            debug_assert!(elems.len() >= 2);
            elems.sort_by_key(|wire| wire.0);
            let min = elems[0].0;
            let max = elems[1].0;

            // Find a valid range in which to insert this
            let overlaps = self.blocked.get_overlaps(min..=max);
            let longest = elems
                .iter()
                .map(|(wire, _)| self.wires[*wire].len())
                .max()
                .unwrap();
            let moment = match overlaps.binary_search(&longest) {
                // in the overlaps set, must go farther ahead.
                Ok(mut idx) => loop {
                    let idx_wire = overlaps[idx]; // double lookup
                    let next = idx + 1;
                    if let Some(next_wire) = overlaps.get(next) {
                        if next_wire - idx_wire >= 2 {
                            break idx_wire + 1;
                        }
                    } else {
                        // `idx` was the last index
                        break idx_wire + 1;
                    }
                    idx = next;
                },
                // Not in the overlaps set: can just push. No caching.
                Err(_) => longest,
            };

            for (wire, elem) in elems {
                // The single-wire invariants aren't checked when we push a multiple-wire gate!
                let wire = &mut self.wires[wire];
                wire.extend_to(moment);
                wire.unchecked_push(elem);
            }

            for wire in &mut self.wires[min..=max] {
                wire.invalidate_blocked();
            }

            self.blocked.insert(min..=max, moment);
        }
    }

    impl FmtWith<LaTeX> for LayoutState<Elem> {
        #[rustfmt::skip]
        fn fmt(&self, latex: &LaTeX, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Occupied(elem) => write!(f, "{}", elem.fmt_with(latex)),
                Free(Dead)  => f.write_str(" "),
                Free(LiveQ) => f.write_str(r"\qw"),
                Free(LiveC) => f.write_str(r"\cw"),
            }
        }
    }

    impl FmtWith<LaTeX> for Wire {
        #[rustfmt::skip]
        fn fmt(&self, latex: &LaTeX, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if let Some((last, head)) = &self.cells.split_last() {
                for cell in head.iter() {
                    // Prev comment: "must not be a raw string"; why?
                    write!(f, "{} & ", cell.fmt_with(latex))?;
                }
                write!(f, "{} ", last.fmt_with(latex))?;
            }
            Ok(())
        }
    }

    impl FmtWith<LaTeX> for LayoutArray<'_> {
        fn fmt(&self, latex: &LaTeX, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if latex.standalone {
                writeln!(f, "{}", LaTeX::HEADER)?;
            }
            writeln!(f, "{}", LaTeX::BEGIN_ENV)?;
            if let Some((last, head)) = &self.wires.split_last() {
                for wire in head.iter() {
                    writeln!(f, "{}\\\\", wire.fmt_with(latex))?;
                }
                writeln!(f, "{}", last.fmt_with(latex))?;
            }
            writeln!(f, "{}", LaTeX::END_ENV)?;
            if latex.standalone {
                writeln!(f, "{}", LaTeX::FOOTER)?;
            }
            Ok(())
        }
    }

    impl LaTeX {
        const HEADER: &'static str = r"\documentclass{standalone}
\usepackage{tikz}
\usetikzlibrary{quantikz}
\usepackage[T1]{fontenc}
\begin{document}";

        const FOOTER: &'static str = r"\end{document}";

        const BEGIN_ENV: &'static str = r"\begin{quantikz}";

        const END_ENV: &'static str = r"\end{quantikz}";
    }

    impl Target for LaTeX {
        #[rustfmt::skip]
        fn from(&self, circ: CircuitBuf) -> ObjectCode {
            let qbits = circ.qbit_size();
            let cbits = circ.cbit_size();
            let mut layout_array = LayoutArray::new(self, qbits, cbits);

            for inst in circ.into_iter() {
                layout_array.push_inst(inst);
            }

            format!("{}", layout_array.fmt_with(self))
        }
    }
}
