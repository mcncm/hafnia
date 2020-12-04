/// In this module we outline the Backend api. This is pretty unstable for the
/// time being, so don’t rely on it.

/// Compilation targets, if the compiler is configured to produce an object file.
pub mod target {
    use crate::circuit::{Circuit, Gate};

    pub trait TargetSerializable<T> {
        fn to_target(&self) -> T;
    }

    /////////////////
    // Null target //
    /////////////////

    pub struct NullTarget();

    //////////////
    // OpenQASM //
    //////////////

    /// There is a version 3 of QASM, but we’re only going to use 2.0 for now, since
    /// this is what Cirq supports.
    pub const QASM_VERSION: &str = "2.0";

    /// The Qasm object code type is just a wrapper around a String.
    pub struct Qasm(pub String);

    impl TargetSerializable<Qasm> for Circuit {
        fn to_target(&self) -> Qasm {
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
                .map(|gate| gate.to_target().0)
                .collect::<Vec<String>>()
                .join("\n");
            Qasm(format!(
                "OPENQASM {};\ninclude \"qelib1.inc\";\n{}\n{}\n",
                QASM_VERSION, declaration, gates
            ))
        }
    }

    ///////////
    // LaTeX //
    ///////////

    pub const LATEX_HEADER: &str = r#"
    \documentclass{article}
    \begin{document}
    "#;

    pub const LATEX_FOOTER: &str = r#"
    \end{document}
    "#;

    /// This backend emits a circuit in qcircuit format
    pub struct Latex(pub String);

    /// Serialize as a quantikz circuit
    impl TargetSerializable<Latex> for Circuit {
        fn to_target(&self) -> Latex {
            Latex(format!("{}{}{}", LATEX_HEADER, "", LATEX_FOOTER))
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
