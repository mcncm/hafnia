use crate::alloc::Allocator;
use crate::hafnia_errors::ErrorBuf;
use crate::circuit::Qubit;

fn is_power_of_two(n: usize) -> bool {
    (n > 0) & (n & (n - 1) == 0)
}

/// A quantum random access memory
///
/// This is the structure of the Qram bucket brigade:
/// ```text
///             [ | ]
///            /     \
///           /       \
///       [ | ]       [ | ]
///       /   \       /   \
///     [ ]   [ ]   [ ]   [ ]
/// ```
/// Each internal node contains two qubits, because we assume not to have access
/// to true qutrits. It is probably a worthwhile (if slightly marginal) research
/// problem to figure out how to use the routing qubits more efficiently.
/// Following [Giovanetti et al.](https://arxiv.org/abs/0708.1879), we say that
/// there are `N = 2^n` memory cells addressed by n qubits. There are therefore
/// `N + 2 * (N - 1)` qubits
///
/// The three states of the internal nodes shall be:
/// `|wait⟩ := |00⟩`, `|left⟩ := |10⟩`, `|right⟩ := |01⟩`
pub struct Qram {
    pub size: usize,
    arena: Vec<Qubit>,
    // The Qram is also an allocator in its own right. Consider whether this
    // functionality is orthogonal to--and should be separated from--the bucket
    // brigade implementation.
    least_free: usize,
}

#[derive(PartialEq, Eq)]
enum QramLayer {
    // pos < N - 2
    NodeUpper,
    // pos < 2 * (N - 1)
    NodeLower,
    // pos >= 2 * (N - 1)
    Leaf,
}

impl Qram {
    pub fn new(allocator: &mut dyn Allocator<Qubit>, size: usize) -> Self {
        assert!(is_power_of_two(size));
        // Should be able to promise that there are enough qubits for the QRAM!
        let arena = allocator.alloc(Self::arena_len(size)).unwrap();
        Self {
            size,
            arena,
            least_free: 0,
        }
    }

    fn arena_len(size: usize) -> usize {
        size + 2 * (size - 1)
    }

    fn layer_of(&self, pos: usize) -> QramLayer {
        use QramLayer::*;
        if pos < self.size - 2 {
            NodeUpper
        } else if pos < 2 * (self.size - 1) {
            NodeLower
        } else if pos < self.size {
            Leaf
        } else {
            unreachable!();
        }
    }

    fn child_l(&self, pos: usize) -> Option<usize> {
        use QramLayer::*;
        match self.layer_of(pos) {
            NodeUpper => Some(2 * (pos + 1)),
            NodeLower => Some(pos + self.size),
            Leaf => None,
        }
    }

    fn child_r(&self, pos: usize) -> Option<usize> {
        use QramLayer::*;
        match self.layer_of(pos) {
            NodeUpper => Some(2 * (pos + 2)),
            NodeLower => Some(pos + self.size + 1),
            Leaf => None,
        }
    }

    #[inline(always)]
    fn sig_fst(&self, pos: usize) -> Qubit {
        assert!(self.layer_of(pos) != QramLayer::Leaf);
        self.arena[pos]
    }

    #[inline(always)]
    fn sig_snd(&self, pos: usize) -> Qubit {
        assert!(self.layer_of(pos) != QramLayer::Leaf);
        self.arena[pos + 1]
    }
}

impl Allocator<Qubit> for Qram {
    fn alloc(&mut self, n: usize) -> Result<Vec<Qubit>, ErrorBuf> {
        // This implementation is copied directly from that of QubitAllocator.
        // This is not so bad today, but you should either decide on a mechanism
        // to keep them in step with one another, or a reason to prefer
        // different allocation algorithms for the two.
        let end = self.least_free + n;
        if self.size < end {
            // Should fail if we run out of qubits!
            todo!();
        }
        let qubits = (self.least_free..end).collect();
        self.least_free = end;
        Ok(qubits)
    }

    /// Yes, this is a no-op.
    fn free(&mut self, _addr: usize) {}
}

pub mod test {
    use super::*;
    use crate::alloc::QubitAllocator;
    use crate::arch::Arch;

    /// Just eliminates unused variable warnings from path macro
    #[allow(unused_variables)]
    fn noop(pos: usize) {}

    /// I’m not really sure *why* it complains about this not being used.
    #[allow(unused_macros)]
    macro_rules! path {
        ($qram:ident => $($direction:ident),*) => {
            let mut pos = 0;
            $(pos = $qram.$direction(pos).unwrap();)*
            noop(pos)
        };
    }

    #[test]
    fn paths_work() {
        // #![allow(unused_mut)]
        let arch = Arch::default();
        let mut alloc = QubitAllocator::new(arch);
        let qram = Qram::new(&mut alloc, 8);
        path![ qram => child_l, child_l, child_l ];
        path![ qram => child_l, child_l, child_r ];
        path![ qram => child_l, child_r, child_l ];
        path![ qram => child_l, child_r, child_r ];
        path![ qram => child_r, child_l, child_l ];
        path![ qram => child_r, child_l, child_r ];
        path![ qram => child_r, child_r, child_l ];
        path![ qram => child_r, child_r, child_r ];
    }

    #[test]
    #[should_panic]
    fn path_too_long() {
        // #![allow(unused_mut)]
        let arch = Arch::default();
        let mut alloc = QubitAllocator::new(arch);
        let qram = Qram::new(&mut alloc, 8);
        path![ qram => child_l, child_l, child_l, child_l ];
    }
}
