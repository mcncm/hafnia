/// In this module we outline the backend APIs. This is all pretty unstable for the
/// time being, so don’t rely on it.

/// Compilation targets, if the compiler is configured to produce an object file.
pub mod target {
    use crate::interpreter::Interpreter;

    /// This is a marker trait for compile targets
    pub trait Target<'a>: std::fmt::Debug {
        type ObjectCode;

        fn from(&self, interp: &Interpreter<'a>) -> Self::ObjectCode;
    }

    /// This trait is implemented by internal structs which, during code
    /// generation, need inform the target safely about their private fields.
    pub trait IntoTarget<'a, T>
    where
        T: Target<'a>,
    {
        // FIXME Consider changing the name: in Rust, it is conventional for
        // methods called `into` to take by value.
        fn into_target(&self, target: &T) -> T::ObjectCode;
    }

    /////////////////
    // Null target //
    /////////////////

    #[derive(Debug)]
    pub struct NullTarget();
    impl<'a> Target<'a> for NullTarget {
        type ObjectCode = ();

        fn from(&self, _interp: &Interpreter<'a>) {}
    }

    //////////////
    // OpenQASM //
    //////////////

    /// There is a version 3 of QASM, but we’re only going to use 2.0 for now, since
    /// this is what Cirq supports.
    pub const QASM_VERSION: &str = "2.0";

    /// The Qasm object code type is just a wrapper around a String.
    #[derive(Debug)]
    pub struct Qasm;

    impl Qasm {
        fn bindings(&self, env: &crate::environment::Environment) -> String {
            format!("// {}", env.into_target(self))
        }

        fn headers(&self) -> String {
            format!("OPENQASM {};\ninclude \"qelib1.inc\";", QASM_VERSION)
        }

        fn circuit(&self, circuit: &crate::circuit::Circuit) -> String {
            circuit.into_target(self)
        }
    }

    impl<'a> Target<'a> for Qasm {
        type ObjectCode = String;

        fn from(&self, interp: &Interpreter<'a>) -> String {
            format!(
                "{}\n{}\n{}",
                self.bindings(&interp.env),
                self.headers(),
                self.circuit(&interp.circuit)
            )
        }
    }

    impl IntoTarget<'_, Qasm> for crate::circuit::Circuit {
        fn into_target(&self, target: &Qasm) -> String {
            let declaration = {
                if let Some(max_qubit) = self.max_qubit {
                    let qubits = max_qubit + 1;
                    format!("qreg q[{}];\ncreg c[{}];", qubits, qubits)
                } else {
                    String::new()
                }
            };
            let gates = self
                .circ_buf
                .iter()
                .map(|gate| gate.into_target(target))
                .collect::<Vec<String>>()
                .join("\n");
            format!("{}\n{}\n", declaration, gates)
        }
    }

    impl<'a> IntoTarget<'a, Qasm> for crate::interpreter::Interpreter<'a> {
        fn into_target(&self, target: &Qasm) -> String {
            let bindings_asm = self.env.into_target(target);
            let circuit_asm = self.circuit.into_target(target);
            format!("//{}\n{}", bindings_asm, circuit_asm)
        }
    }

    ///////////
    // LaTeX //
    ///////////

    // TODO the public interface and private implementation are a bit mixed
    // here: there is some functionality in the `diagram` function of `Latex`
    // that should probably go in the `new` constructor of `LayoutArray`.

    /// This backend emits a circuit in qcircuit format
    #[derive(Debug)]
    pub struct Latex;

    /// The three cell states in a common quantum circuit: in `Some(T)`, the
    /// cell is occupied by a gate. In `None`, there is no gate or blocking
    /// element. In `Blocked` there is no gate, but the cell is obstructed, as
    /// by a vertical wire.
    #[derive(Clone, PartialEq)]
    enum LayoutState<T: Clone + PartialEq> {
        Some(T),
        None,
        Blocked,
    }

    type Wire<T> = Vec<LayoutState<T>>;

    /// A private struct used by the Latex backend to lay out the circuit
    /// representation. The index order is space-major, because this should have
    /// better locality of reference, and easier to serialize without an extra
    /// allocation.
    struct LayoutArray {
        arr: Vec<Wire<String>>,
        /// On each wire, the index of the first `None` cell, of which there is
        /// guaranteed to be at least one.
        first_free: Vec<usize>,
    }

    impl LayoutArray {
        fn new(wires: usize) -> Self {
            // Start with length at least one. It will be an invariant of this
            // data structure that there is always an empty final moment. This
            // final moment will provide the terminal $\qw$ on each wire.
            //
            // (In fact, as a convenience we'll include *two* empty moments. The
            // first of these will be the initial $\qw$ on each wire.)
            //
            // It is also an invariant that there's at least one wire, that
            // should be enforced by `new`, although it isn't yet in a *natural* way.
            assert!(wires > 0);
            Self {
                arr: vec![vec![LayoutState::Blocked, LayoutState::None]; wires],
                first_free: vec![1; wires],
            }
        }

        #[inline(always)]
        fn wires(&self) -> usize {
            // This is safe because we’re always guaranteed to contain at least
            // one moment.
            self.arr.len()
        }

        #[inline(always)]
        fn add_moment(&mut self) {
            for wire in self.arr.iter_mut() {
                wire.push(LayoutState::None);
            }
        }

        #[inline(always)]
        fn len(&self) -> usize {
            // Safe because we are guaranteed to always have at least one wire.
            unsafe { self.arr.get_unchecked(0).len() }
        }

        /// Returns true if and only if the range of wires between `lower` and
        /// `upper` (inclusive!) is all free.
        fn range_free(&self, moment: usize, range: std::ops::RangeInclusive<usize>) -> bool {
            self.arr[range]
                .iter()
                .all(|wire| wire[moment] == LayoutState::None)
        }

        #[rustfmt::skip]
        fn push_gate(&mut self, gate: &crate::circuit::Gate) {
            use crate::circuit::Gate::*;
            match gate {
                X(tgt)           => self.insert_single(tgt, r"\gate{X}".to_string()),
                T { tgt, conj }  => self.insert_single(tgt, {
                    if *conj {
                        r"\gate{T^\dag}".to_string()
                    } else {
                        r"\gate{T}".to_string()
                    }
                }),
                H(tgt)           => self.insert_single(tgt, r"\gate{H}".to_string()),
                Z(tgt)           => self.insert_single(tgt, r"\gate{Z}".to_string()),
                CX { ctrl, tgt } => {
                    let dist = (*tgt as isize) - (*ctrl as isize);
                    let ctrl_label = format!(r"\ctrl{{{}}}", dist);
                    let ctrl = (ctrl, ctrl_label);
                    let tgt = (tgt, r"\targ{}".to_string());
                    self.insert_multiple(vec![ctrl, tgt]);
                }
                M(tgt)           => self.insert_single(tgt, r"\meter{}".to_string()),
            }
        }

        fn insert_single(&mut self, wire: &usize, gate: String) {
            let wire = *wire;
            let mut moment = self.first_free[wire];
            self.arr[wire][moment] = LayoutState::Some(gate);

            while moment < self.len() - 1 {
                moment += 1;
                if self.arr[wire][moment] == LayoutState::None {
                    self.first_free[wire] = moment;
                    return;
                }
            }

            // There are no empty cells on this wire!
            self.add_moment();
            self.first_free[wire] = self.len() - 1;
        }

        fn insert_multiple(&mut self, gates: Vec<(&usize, String)>) {
            // NOTE: is there a single iterator adapter in the standard library
            // for getting both the min and max in one go?
            let min = **gates.iter().map(|(wire, _)| wire).min().unwrap();
            let max = **gates.iter().map(|(wire, _)| wire).max().unwrap();
            // For now, we'll do the most naive possible correct thing: we'll *always*
            // insert these at the end of the circuit.
            if !self.range_free(self.len() - 1, min..=max) {
                self.add_moment();
            }
            let moment = self.len() - 1;
            for (&wire, gate) in gates.into_iter() {
                self.arr[wire][moment] = LayoutState::Some(gate);
                self.first_free[wire] = moment + 1;
            }
            // FIXME We'll also do this suboptimally: we'll do a second pass
            // through the range, changing everything still free into Blocked.
            // We *could* do this in a single pass if we sorted `gates`. Note
            // that the range is *ex*clusive, because we can’t have the
            // ends of a CNOT being free.
            for wire in (min + 1)..max {
                if self.arr[wire][moment] == LayoutState::None {
                    self.arr[wire][moment] = LayoutState::Blocked;
                }
            }
            self.add_moment();
        }
    }

    impl IntoTarget<'_, Latex> for LayoutArray {
        fn into_target(&self, _target: &Latex) -> String {
            self.arr
                .iter()
                .map(|wire| {
                    wire.iter()
                        .map(|gate| match gate {
                            LayoutState::Some(gate) => gate,
                            _ => r"\qw",
                        })
                        .collect::<Vec<&str>>()
                        .join(" & ")
                })
                .collect::<Vec<String>>()
                // Must not be a raw string; we really want to emit a newline!
                .join(" \\\\\n")
        }
    }

    impl Latex {
        const HEADER: &'static str = r"\documentclass{standalone}
\usepackage{tikz}
\usetikzlibrary{quantikz}
\begin{document}
\begin{quantikz}
";

        const FOOTER: &'static str = r"
\end{quantikz}
\end{document}
";

        fn diagram(&self, circuit: &crate::circuit::Circuit) -> String {
            let max_qubit = match circuit.max_qubit {
                Some(qb) => qb,
                None => {
                    return String::new();
                }
            };

            let mut layout_array = LayoutArray::new(max_qubit + 1);

            for gate in circuit.circ_buf.iter() {
                layout_array.push_gate(gate);
            }

            layout_array.into_target(self)
        }
    }

    impl<'a> Target<'a> for Latex {
        type ObjectCode = String;

        fn from(&self, interp: &Interpreter<'a>) -> Self::ObjectCode {
            format!(
                "{}{}{}",
                Self::HEADER,
                self.diagram(&interp.circuit),
                Self::FOOTER
            )
        }
    }
}

/// This module contains types for describing target architectures
pub mod arch {
    use std::cmp::{Ordering, PartialOrd};
    use std::convert::From;

    /// The number of qubits acccessible to a given architecture. Its ordering
    /// should be the natural one for something that’s maybe infinite:
    ///
    /// # Examples
    /// ```
    /// # use cavy::backend::arch::QbCount;
    /// let c1 = QbCount::Finite(0);
    /// let c2 = QbCount::Finite(1);
    /// let c3 = QbCount::Infinite;
    /// assert!(c1 < c2);
    /// assert!(c2 < c3);
    /// ```
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub enum QbCount {
        Finite(usize),
        Infinite,
    }

    impl From<usize> for QbCount {
        fn from(num: usize) -> Self {
            QbCount::Finite(num)
        }
    }

    impl Default for QbCount {
        fn default() -> Self {
            Self::Infinite
        }
    }

    /// This is the main device architecture struct that describes the qubit
    /// layout, native gates, and related constraints.
    #[derive(Default)]
    pub struct Arch {
        pub qb_count: QbCount,
    }
}
