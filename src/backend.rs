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
        // TODO consider using the Serde API, which is of course pretty standard
        // in Rust. Maybe that accomplishes the same thing without the awkward
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

    /// This backend emits a circuit in qcircuit format
    #[derive(Debug)]
    pub struct Latex;

    /// A private struct used by the Latex backend to lay out the circuit representation.
    struct LayoutArray(Vec<Vec<String>>);

    impl LayoutArray {
        #[rustfmt::skip]
        fn push_gate(&mut self, gate: &crate::circuit::Gate) {
            use crate::circuit::Gate::*;
            match gate {
                X(tgt)           => self.0[*tgt].push(r"\gate{X}".to_string()),
                T { tgt, conj }  => self.0[*tgt].push({
                    if *conj {
                        r"\gate{T}".to_string()
                    } else {
                        r"\gate{T^\dag}".to_string()
                    }
                }),
                H(tgt)           => self.0[*tgt].push(r"\gate{H}".to_string()),
                Z(tgt)           => self.0[*tgt].push(r"\gate{Z}".to_string()),
                CX { .. } => todo!(),
                M(_)           => todo!(),
            }
        }

        /// After all gates have been pushed, some of the wires will be too
        /// short. These need empty cells added to them.
        fn equalize_wires(&mut self) {
            if self.0.is_empty() {
                return;
            }

            // At this point, are guaranteed to have at least one wire, so this
            // unwrap is safe.
            let length = self.0.iter().map(|wire| wire.len()).max().unwrap();
            for wire in &mut self.0 {
                for _ in 0..(length - wire.len()) {
                    wire.push(r"\qw".to_string());
                }

                // Finally, the wires are all the right length and we can cap
                // them all with a \qw.
                wire.push(r"\qw ".to_string());
            }
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

            let mut layout_array = LayoutArray(vec![vec![String::new()]; max_qubit + 1]);
            for gate in circuit.circ_buf.iter() {
                layout_array.push_gate(gate);
            }
            layout_array.equalize_wires();

            layout_array
                .0
                .iter()
                .map(|wire| wire.join(" & "))
                .collect::<Vec<String>>()
                // Must not be a raw string; we really want to emit a newline!
                .join("\\\\\n")
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
