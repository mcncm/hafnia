/// This module contains types for describing execution environment
/// architectures.
use std::cmp::{Ordering, PartialOrd};
use std::convert::From;

/// The number of qubits acccessible to a given architecture. Its ordering
/// should be the natural one for something that’s maybe infinite:
///
/// # Examples
/// ```
/// # use cavy_core::arch::QbCount;
/// let c1 = QbCount::Finite(0);
/// let c2 = QbCount::Finite(1);
/// let c3 = QbCount::Infinite;
/// assert!(c1 < c2);
/// assert!(c2 < c3);
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum QbCount {
    Finite(usize),
    Infinite,
}

impl From<usize> for QbCount {
    fn from(num: usize) -> Self {
        QbCount::Finite(num)
    }
}

impl From<Option<usize>> for QbCount {
    fn from(num: Option<usize>) -> Self {
        match num {
            Some(num) => Self::Finite(num),
            None => Self::Infinite,
        }
    }
}

impl Default for QbCount {
    fn default() -> Self {
        Self::Infinite
    }
}

/// This enum describes the possible ways that measurement might act on a qubit.
#[derive(Debug, Clone, Copy)]
pub enum MeasurementMode {
    /// In this mode, a measured qubit is assumed to be in the |0> state.
    Demolition,
    /// In this mode, a measured qubit is in the same state as its measured
    /// value.
    Nondemolition,
}

impl Default for MeasurementMode {
    fn default() -> Self {
        Self::Demolition
    }
}

/// This is the main device architecture struct that describes the qubit
/// layout, native gates, and related constraints.
///
/// TODO Enforce that qram_size <= qb_count
#[derive(Default, Debug, Clone, Copy)]
pub struct Arch {
    pub qb_count: QbCount,
    pub qram_size: usize,
    pub meas_mode: MeasurementMode,
    /// Whether classical feedback is enabled for this architecture
    pub feedback: bool,
    /// Whether arbitrary recursion (or, equivalently, diverging loops) are
    /// enabled for this architecture
    pub recursion: bool,
}
