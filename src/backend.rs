/// In this module we outline the Backend api. This is pretty unstable for the
/// time being, so don’t rely on it.

/// There is a version 3 of QASM, but we’re only going to use 2.0 for now, since
/// this is what Cirq supports.
pub const QASM_VERSION: &str = "2.0";

pub trait Backend {
    type CodeObject;
}

pub trait BackendSerializable<T: Backend> {
    fn to_backend(&self) -> T::CodeObject;
}

///////////////////////
// Concrete Backends //
///////////////////////

pub struct NullBackend {}
impl Backend for NullBackend {
    type CodeObject = ();
}

impl NullBackend {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct Qasm {}
impl Backend for Qasm {
    type CodeObject = String;
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
