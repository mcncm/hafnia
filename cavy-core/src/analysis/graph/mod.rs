//! Some fundamental graph analyses: dominators and postdominators,
//! reachability, and more.

use crate::mir::BlockId;
use crate::store::Store;

use super::dataflow::*;
use bitvec::prelude::*;

/// Graph algorithms
mod algorithm;
pub mod dominators;

pub use algorithm::{traversals, Digraph, Postorder, Preorder};
pub use dominators::DominatorAnalysis;

// We're going to interpret a `BitVec` as a set, whose elements are its nonzero
// bits. For internal debugging use only.
impl std::fmt::Display for Store<BlockId, BitVec> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("per-block sets:\n")?;
        for (blk, bitv) in self.idx_enumerate() {
            write!(f, "\t{} [", blk)?;
            let mut elems =
                bitv.iter()
                    .enumerate()
                    .filter_map(|(place, bit)| if *bit { Some(place) } else { None });
            if let Some(head) = elems.next() {
                write!(f, "{}", head)?;
                for elem in elems {
                    write!(f, ", {}", elem)?;
                }
            }
            f.write_str("]\n")?;
        }
        Ok(())
    }
}
