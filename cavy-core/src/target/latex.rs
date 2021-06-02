//! The LaTeX backend, which currently uses quantikz, and which should not be
//! too hard to use with qcircuit as well--the layout engine should be the  package called
//! `yquant`, which should be pretty much trivial to support.

use std::{
    fmt, iter,
    ops::{Index, IndexMut, RangeInclusive},
};

use crate::circuit::*;
use crate::context::SymbolId;

use super::*;

/// LaTeX quantum circuit packages
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Package {
    Quantikz { nwtarg: bool, wave: bool },
    Qcircuit { nwtarg: bool },
    Yquant,
}

// There should be no harm in bringing all of these into module scope.
use Package::*;

impl Default for Package {
    fn default() -> Self {
        Self::Quantikz {
            nwtarg: false,
            wave: false,
        }
    }
}

/// This backend emits a circuit in quantikz format
pub struct LaTeX {
    /// Include preamble and `\begin{document}...\end{document}`?
    pub standalone: bool,
    /// Instead of writing initial `X` gates, write the nominal input state
    pub initial_kets: bool,
    /// The quantum circuit package to use for rendering
    pub package: Package,
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
        !(&self.high < other.start() || other.end() < &self.low)
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
    X, Z, H, T, TDag, S, SDag, Phase(Option<f32>),
    // A quantum control label with a distance to its target
    QCtrl(isize, bool),
    // A swap label with a distance to its target
    Swap(isize),
    // A control target, with an optional incoming wire
    Targ(Liveness),
    // A classical control target. With some target options, this uses a custom command
    // in order to have no incoming wires.
    // NOTE: this should be deprecated in favor of `Targ` with a liveness option
    CTarg(Option<isize>),
    // An classical control label with a distance to its target
    CCtrl(isize, bool),
    // A swap target
    TargX,
    // Trash a qubit
    Trash,
    // A meter with an optional control line
    Meter(Option<isize>),
    // A label for IO data
    IoLabel(Box<IoLabelData>),
    // The quantikz wave
    Wave
}

#[derive(Debug, Clone)]
struct IoLabelData {
    /// The name of the IO object being written to
    name: SymbolId,
    /// The index within the IO object being output to
    elem: usize,
}

impl<'c> FmtWith<(&LaTeX, &Context<'c>)> for Elem {
    fn fmt(&self, (latex, ctx): &(&LaTeX, &Context), f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Elem::*;
        match self {
            Ket(s) => {
                if let Qcircuit { .. } = latex.package {
                    write!(f, r"\lstick{{\ket{{{}}}}}", s)
                } else {
                    // Package is Quantikz
                    write!(f, r"\lstick{{$\ket{{{}}}$}}", s)
                }
            }
            X => f.write_str(r"\gate{X}"),
            Z => f.write_str(r"\gate{Z}"),
            H => f.write_str(r"\gate{H}"),
            T => f.write_str(r"\gate{T}"),
            TDag => f.write_str(r"\gate{T^\dag}"),
            S => f.write_str(r"\gate{S}"),
            SDag => f.write_str(r"\gate{S^\dag}"),
            Phase(phase) => {
                if let Quantikz { .. } = latex.package {
                    if let Some(phase) = phase {
                        write!(f, r"\phase{{{}}}", phase)
                    } else {
                        write!(f, r"\phase{{}}")
                    }
                } else {
                    unimplemented!("Can't format this gate yet for this package");
                }
            }
            QCtrl(dist, true) => write!(f, r"\ctrl{{{}}}", dist),
            QCtrl(dist, false) => write!(f, r"\octrl{{{}}}", dist),
            Targ(liveness) => match liveness {
                Dead if latex.uses_nwtarg() => f.write_str(r"\nwtarg{}"),
                LiveC if latex.uses_nwtarg() => f.write_str(r"\nwtarg{} \cw"),
                _ => f.write_str(r"\targ{}"),
            },

            CTarg(dist) => {
                if latex.uses_nwtarg() {
                    f.write_str(r"\nwtarg{}")?;
                } else {
                    f.write_str(r"\cw")?;
                }

                if let Some(dist) = dist {
                    debug_assert!(matches!(latex.package, Qcircuit { .. }));
                    write!(f, r"\cwx[{}]", dist)?;
                }
                Ok(())
            }
            CCtrl(dist, true) => {
                if !matches!(latex.package, Quantikz { .. }) {
                    todo!();
                }

                write!(f, r"\cwbend{{{}}}", dist)
            }
            CCtrl(_dist, false) => {
                todo!();
            }
            Swap(dist) => write!(f, r"\swap{{{}}}", dist),
            TargX => f.write_str(r"\targX{}"),
            Trash => f.write_str(r"\trash{}"),
            Meter(targ) => match (latex.package, targ) {
                (Quantikz { .. }, Some(dist)) => write!(f, r"\meter{{}} \vcw{{{}}}", dist),
                (Qcircuit { .. }, Some(dist)) => write!(f, r"\meter{{}} \cwx[{}]", dist),
                (_, None) => f.write_str(r"\meter{}"),
                _ => unreachable!(),
            },
            // Maybe "ought" to use `\rstick` here, but then we'd need to figure
            // out the bounding box for Qcircuit.
            IoLabel(io) => {
                let name = LaTeX::escape(&format!("{}", io.name.fmt_with(ctx)));
                match latex.package {
                    Qcircuit { .. } => {
                        write!(f, r"\push{{\tt \enspace {}[{}] }} \cw", name, io.elem)
                    }
                    Quantikz { .. } => write!(f, r"\rstick{{\tt {}[{}] }} \cw", name, io.elem),
                    _ => unreachable!(),
                }
            }
            Wave => f.write_str(r"\wave"),
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

    // NOTE: a key invariant is that no wire is ever empty. So, we can
    // get the last cell unconditionally.
    pub fn last(&self) -> &LayoutState<Elem> {
        self.cells.last().unwrap()
    }

    pub fn last_mut(&mut self) -> &mut LayoutState<Elem> {
        self.cells.last_mut().unwrap()
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

        if Some(self.len()) == self.next_blocked {
            self.compute_next_free();
        }

        self.extend_to(self.next_free);
        self.cells.push(Occupied(cell));
    }

    /// This name is just a warning
    pub fn push_unchecked(&mut self, cell: Elem) {
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
        debug_assert!(qwires + cwires > 0);
        let wires = iter::repeat_with(|| Wire::new())
            .take(Self::layout_width(latex, qwires, cwires))
            .collect();
        Self {
            latex,
            wires,
            blocked: IntervalMap::new(),
            fst_cwire: Self::first_cwire_index(latex, qwires),
        }
    }

    // Should maybe just compute some `Sections` struct during `new`
    fn layout_width(latex: &LaTeX, qwires: usize, cwires: usize) -> usize {
        let mut width = qwires + cwires;
        match &latex.package {
            Quantikz { wave: true, .. } => width += 1,
            _ => (),
        }
        width
    }

    fn first_cwire_index(latex: &LaTeX, qwires: usize) -> usize {
        let mut cwire = qwires;
        match &latex.package {
            Quantikz { wave: true, .. } => cwire += 1,
            _ => (),
        }
        cwire
    }

    fn len(&self) -> usize {
        self.wires[0].len()
    }

    fn width(&self) -> usize {
        self.wires.len()
    }

    /// Translate from qwire address to absolute address
    #[inline(always)]
    fn qwire(&self, qbit: Qbit) -> usize {
        Into::<u32>::into(qbit) as usize
    }

    /// Translate from cwire address to absolute address
    #[inline(always)]
    fn cwire(&self, cbit: Cbit) -> usize {
        use crate::store::Index;
        Into::<u32>::into(cbit) as usize + self.fst_cwire
    }

    /// How quantikz expects distances to be calculated. Here, `src` denotes
    /// e.g. the source of a control operation; `tgt` denotes its target.
    #[inline(always)]
    fn dist(&self, src: usize, tgt: usize) -> isize {
        (tgt as isize) - (src as isize)
    }

    fn push_inst(&mut self, inst: Inst) {
        match inst {
            Inst::CInit(_) => {}
            Inst::CFree(_, _) => {}
            Inst::QInit(q) => self.qinit(q),
            Inst::QFree(q, s) => self.push_qfree(q, s),
            Inst::QGate(g) => self.push_qgate(g),
            Inst::CGate(g) => self.push_cgate(g),
            Inst::Meas(s, t) => self.push_meas(self.qwire(s), self.cwire(t)),
            Inst::Io(io) => self.push_io_out(&io),
        }
    }

    fn qinit(&mut self, qbit: Qbit) {
        let wire = self.qwire(qbit);
        let wire = &mut self.wires[wire];
        wire.liveness = LiveQ;
        if self.latex.initial_kets {
            let prev = wire.last_mut();
            if let Free(Dead) = prev {
                *prev = Occupied(Elem::Ket("0"));
            }
        }
    }

    fn push_qfree(&mut self, qbit: Qbit, s: FreeState) {
        let wire = self.qwire(qbit);
        if self.wires[wire].liveness == LiveQ {
            match s {
                FreeState::Clean => {}
                FreeState::Dirty => {
                    self.insert_single(wire, Elem::Trash);
                }
            }
            self.wires[wire].liveness = Dead;
        }
    }

    // TODO: clean up where and how wires are made live; eliminate some of these
    // unnecessary clones.
    fn push_qgate(&mut self, gate: GateQ) {
        let (mut base, mut ctrls) = self.qgate_elems(gate);

        if ctrls.is_empty() {
            // We can do this unconditionally instead of inserting: if there’s
            // already a ket, it’s safe to update it, and this doesn’t change the
            // actual gates of the circuit.
            if let (Elem::X, Occupied(ref mut k @ Elem::Ket("0"))) =
                (&base.1, self.wires[base.0].last_mut())
            {
                *k = Elem::Ket("1");
                return;
            }
            self.insert_single(base.0, base.1);
            self.wires[base.0].liveness = LiveQ;
            return;
        }

        // Special-case multi-controlled CZ gates: if no controls, we have
        // already returned.
        if let Elem::Z = base.1 {
            base.1 = Elem::Phase(None);
        }

        // Then just add the base element to the
        ctrls.push(base);
        self.insert_multiple(ctrls.clone());

        for (wire, _) in ctrls.iter() {
            let wire = &mut self.wires[*wire];
            wire.liveness = LiveQ;
        }
    }

    fn qgate_elems(&mut self, gate: GateQ) -> ((usize, Elem), Vec<(usize, Elem)>) {
        use BaseGateQ::*;
        let mut ctrls = vec![];

        let mut base = match gate.base {
            X(u) => (self.qwire(u), Elem::X),
            H(u) => (self.qwire(u), Elem::H),
            Z(u) => (self.qwire(u), Elem::Z),
            T(u) => (self.qwire(u), Elem::T),
            TDag(u) => (self.qwire(u), Elem::TDag),
            S(u) => (self.qwire(u), Elem::S),
            SDag(u) => (self.qwire(u), Elem::SDag),
            Phase(u, phase) => (self.qwire(u), Elem::Phase(Some(phase))),
            Cnot { ctrl, tgt } => {
                let (ctrl, tgt) = (self.qwire(ctrl), self.qwire(tgt));
                let dist = self.dist(ctrl, tgt);
                ctrls.push((ctrl, Elem::QCtrl(dist, true)));

                let targ = Elem::Targ(self.wires[tgt].liveness);
                (tgt, targ)
            }
            Swap(u, v) => {
                let (u, v) = (self.qwire(u), self.qwire(v));
                let dist = self.dist(u, v);
                ctrls.push((u, Elem::Swap(dist)));
                (v, Elem::TargX)
            }
        };

        for ctrl in gate.ctrls.into_iter() {
            let sign = ctrl.1;
            let ctrl = self.qwire(ctrl.0);
            let dist = self.dist(ctrl, base.0);
            ctrls.push((ctrl, Elem::QCtrl(dist, sign)));
        }

        if !(ctrls.is_empty()) {
            if let Elem::X = base.1 {
                base.1 = Elem::Targ(self.wires[base.0].liveness);
            }
        }

        (base, ctrls)
    }

    fn push_cgate(&mut self, gate: GateC) {
        if gate.ctrls.len() > 0 {
            // Let's special-case this like mad: only build the circuit for
            // classical control from one bit.
            if gate.ctrls.len() == 1 {
                match gate.base {
                    C(_) => {}
                    Q(baseq) => match baseq {
                        BaseGateQ::X(tgt) => {
                            let src = gate.ctrls[0];
                            let sign = src.1;
                            let (src, tgt) = (self.cwire(src.0), self.qwire(tgt));
                            let dist = self.dist(src, tgt);
                            let src = (src, Elem::CCtrl(dist, sign));
                            let tgt = (tgt, Elem::X);
                            self.insert_multiple(vec![src, tgt]);
                        }
                        _ => todo!(),
                    },
                }
            } else {
                todo!("I'm sorry, I'm special-casing this path for now.");
            }
            return;
        }

        use BaseGate::*;
        use BaseGateC::*;
        let (wire, elem) = match gate.base {
            C(Not(u)) => (u, Elem::CTarg(None)),
            C(Swap(_, _)) => unimplemented!(),
            C(Copy(_, _)) => todo!(),
            C(Cnot { .. }) => todo!(),
            Q(_) => todo!(),
        };
        let wire = self.cwire(wire);
        self.wires[wire].liveness = LiveC;
        self.insert_single(wire, elem);
    }

    fn push_meas(&mut self, src_wire: usize, tgt_wire: usize) {
        let dist = self.dist(src_wire, tgt_wire);
        let src = (src_wire, Elem::Meter(Some(dist)));
        // The distance is only used if needed--no harm to include it
        // unconditionally. Note the *opposite* sign convention.
        let tgt = (tgt_wire, Elem::CTarg(None));
        self.insert_multiple(vec![src, tgt]);
        self.wires[tgt_wire].liveness = LiveC;

        // FIXME shouldn't actually be unconditional: can depend on whether
        // measurements are demolition or nondemolition.
        self.wires[src_wire].liveness = Dead;
    }

    fn push_io_out(&mut self, io: &IoUse) {
        let wire = self.cwire(io.addr);
        let io = IoLabelData {
            // Nice, I get to clone it *again*! (See `dynamic/gates.rs`)
            name: io.channel.clone(),
            elem: io.elem,
        };
        let elem = Elem::IoLabel(Box::new(io));
        self.insert_single(wire, elem);
    }

    fn insert_single(&mut self, wire: usize, elem: Elem) {
        let blocked = &self.blocked;
        self.wires[wire].push(elem, || blocked.get_contained(&wire));
        // We also have to add this gate to the blocking list. Note that this
        // will add a *lot* of blocked intervals to that data structure, which
        // is using the most naive algorithm. Runtime will be something like
        // O(A^2) in the circuit area.
        self.blocked.insert(wire..=wire, self.wires[wire].len() - 1);
    }

    /// Note that, unlike `insert_single`, the "free slots" aren't
    /// effectively cached for multiple-wire gates. This could get slow.
    fn insert_multiple(&mut self, mut elems: Vec<(usize, Elem)>) {
        debug_assert!(elems.len() >= 2);
        elems.sort_by_key(|wire| wire.0);
        let min = elems.iter().map(|elem| elem.0).min().unwrap();
        let max = elems.iter().map(|elem| elem.0).max().unwrap();

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
            wire.push_unchecked(elem);
        }

        self.block_interval(min..=max, moment);
    }

    fn block_interval(&mut self, range: RangeInclusive<usize>, moment: usize) {
        self.blocked.insert(range.clone(), moment);
        for wire in range {
            self.wires[wire].invalidate_blocked();
        }
    }

    /// Final cleanup and prettification
    fn finish(&mut self) {
        let longest = self.wires.iter().map(|wire| wire.len()).max().unwrap_or(0);
        self.finish_wave(longest);
    }

    fn finish_wave(&mut self, longest: usize) {
        if let Quantikz { wave: true, .. } = &self.latex.package {
            // Yeah, not ideal. Should have a layout struct.
            let wave_index = self.fst_cwire - 1;
            let wave = &mut self.wires[wave_index];
            wave.cells[0] = Occupied(Elem::Wave);
            wave.extend_to(longest);
        }
    }
}

// == Formatting of layout arrays for quantikz and qcircuit ==

impl<'c> FmtWith<(&LaTeX, &Context<'c>)> for LayoutState<Elem> {
    #[rustfmt::skip]
    fn fmt(&self, fmt_data: &(&LaTeX, &Context), f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Occupied(elem) => write!(f, "{}", elem.fmt_with(fmt_data)),
            Free(Dead)  => f.write_str(" "),
            Free(LiveQ) => f.write_str(r"\qw"),
            Free(LiveC) => f.write_str(r"\cw"),
        }
    }
}

impl<'c> FmtWith<(&LaTeX, &Context<'c>)> for Wire {
    #[rustfmt::skip]
    fn fmt(&self, fmt_data: &(&LaTeX, &Context), f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((last, head)) = &self.cells.split_last() {
            for cell in head.iter() {
                // Prev comment: "must not be a raw string"; why?
                write!(f, "{} & ", cell.fmt_with(fmt_data))?;
            }
            write!(f, "{} ", last.fmt_with(fmt_data))?;
        }
        Ok(())
    }
}

impl<'c> FmtWith<(&LaTeX, &Context<'c>)> for LayoutArray<'_> {
    fn fmt(&self, fmt_data: &(&LaTeX, &Context), f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let latex = self.latex;
        latex.fmt_header(f)?;
        latex.fmt_circuit_begin(f)?;
        if let Some((last, head)) = &self.wires.split_last() {
            for wire in head.iter() {
                writeln!(f, r"{}\\", wire.fmt_with(fmt_data))?;
            }
            writeln!(f, "{}", last.fmt_with(fmt_data))?;
        }
        latex.fmt_circuit_end(f)?;
        latex.fmt_footer(f)
    }
}

// == Headers, etc. ==

impl LaTeX {
    fn uses_nwtarg(&self) -> bool {
        match self.package {
            Quantikz { nwtarg: true, .. } | Qcircuit { nwtarg: true } => true,
            // always use \nwtarg in standalone mode
            _ => self.standalone,
        }
    }

    /// Escapes a string by replacing underscores with `\_`
    fn escape(s: &str) -> String {
        str::replace(s, "_", r"\_")
    }

    /// LaTeX header for standalone mode
    fn fmt_header(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.standalone {
            return Ok(());
        }

        let class_options = {
            if let Package::Qcircuit { .. } = self.package {
                // `qcircuit` ket labels are off the margins in `standalone`.
                if self.initial_kets {
                    "[border={25pt 5pt 5pt 5pt}]"
                } else {
                    "[border=5pt]"
                }
            } else {
                ""
            }
        };
        writeln!(f, "\\documentclass{}{{standalone}}", class_options)?;

        self.fmt_tex_packages(f)?;
        f.write_str(
            r"\begin{document}
",
        )
    }

    // NOTE: I could get rid of this entire mess by just putting the whole
    // preambles in separate `.tex` files and `include_str!`in them. But then
    // I'd have to use `bracket,qm` unconditionally, which might slow down
    // Qcircuit slightly. And there is *definitely* no hope of using LaTeX
    // source as a Rust format string.
    /// Package and macro declarations for standalone mode
    fn fmt_tex_packages(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.package {
            Package::Qcircuit { .. } => {
                let options = if self.initial_kets { "[braket,qm]" } else { "" };
                writeln!(f, "\\usepackage{}{{qcircuit}}", options)?
            }
            Package::Quantikz { .. } => f.write_str(concat!(
                r"\usepackage{tikz}
\usetikzlibrary{quantikz}
",
                include_str!("trash_quantikz.tex"),
                include_str!("nwtarg_quantikz.tex")
            ))?,
            Package::Yquant => f.write_str(
                r"\usepackage{tikz}
\usepackage{yquant}
",
            )?,
        };
        let common = r"\usepackage[T1]{fontenc}
";
        f.write_str(common)
    }

    #[rustfmt::skip]
    fn fmt_circuit_begin(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let circuit_begin = match self.package {
            Package::Qcircuit { .. } => r"\Qcircuit @C=1em @R=0.7em {
",
            Package::Quantikz { .. } => r"\begin{quantikz}
",
            Package::Yquant =>   r"\begin{tikzpicture}
\begin{yquant}
",
        };
        f.write_str(circuit_begin)
    }

    #[rustfmt::skip]
    fn fmt_circuit_end(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let circuit_end = match self.package {
            Package::Qcircuit { .. } => r"}
",
            Package::Quantikz { .. } => r"\end{quantikz}
",
            Package::Yquant =>   r"\end{tikzpicture}
\end{yquant}
",
        };
        f.write_str(circuit_end)
    }

    fn fmt_footer(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.standalone {
            return Ok(());
        }
        f.write_str(
            r"\end{document}
",
        )
    }
}

impl Target for LaTeX {
    #[rustfmt::skip]
    fn from(&self, circ: CircuitBuf, ctx: &Context) -> ObjectCode {
        let qbits = circ.qbit_size();
        let cbits = circ.cbit_size();
        let mut layout_array = LayoutArray::new(self, qbits, cbits);

        for inst in circ.into_iter() {
            layout_array.push_inst(inst);
        }
        layout_array.finish();

        format!("{}", layout_array.fmt_with(&(self, ctx)))
    }
}

// == boilerplate impls ==

impl<K, V> std::fmt::Debug for Interval<K, V>
where
    K: std::fmt::Debug + Ord,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}, {:?}]: {:?}", self.low, self.high, self.data)
    }
}

impl<K, V> std::fmt::Debug for IntervalMap<K, V>
where
    K: std::fmt::Debug + Ord + Copy,
    V: std::fmt::Debug + Ord + Copy,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for interval in &self.intervals {
            writeln!(f, "{:?}", interval)?;
        }
        Ok(())
    }
}
