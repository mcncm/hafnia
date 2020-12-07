/// This module contains types for describing execution environment
/// architectures.
use std::cmp::{Ordering, PartialOrd};
use std::convert::From;

/// The number of qubits acccessible to a given architecture. Its ordering
/// should be the natural one for something that’s maybe infinite:
///
/// # Examples
/// ```
/// # use cavy::arch::QbCount;
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
