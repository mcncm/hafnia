//! Some helpful formatting implementations, particularly for debugging the
//! results of statementwise dataflow analyses

use std::fmt::{Debug, Display, Formatter, Write};

use crate::{mir::BlockId, store::Store, util::FmtWith};

use super::dataflow::{DataflowCtx, Lattice};

// Let's assume that *any* such store contains statementwise analysis results
impl<'a, T> FmtWith<DataflowCtx<'a>> for Store<BlockId, Vec<T>>
where
    T: Display,
{
    fn fmt(&self, context: &DataflowCtx<'_>, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (blk_id, data) in self.idx_enumerate() {
            // Write the block headline
            let block = &context.gr[blk_id];
            writeln!(f, "{} :: {}", blk_id, block.kind)?;

            let elems: Vec<_> = data.iter().map(|elem| format!("{}", elem)).collect();
            let len = elems.iter().map(|elem| elem.len()).max().unwrap_or(0);
            for (elem, stmt) in elems.iter().zip(block.stmts.iter()) {
                writeln!(f, "\t{:<width$}{}", elem, stmt, width = len + 4)?;
            }

            f.write_str("\n")?;
        }
        Ok(())
    }
}

// And we'll assume that any store shaped like this contains blockwise analysis results
impl<'a, L: Lattice> FmtWith<DataflowCtx<'a>> for Store<BlockId, L>
where
    L: Debug + Lattice,
{
    fn fmt(&self, _context: &DataflowCtx<'_>, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (blk_id, data) in self.idx_enumerate() {
            writeln!(f, "{} \t: {:?}", blk_id, data)?;
        }
        Ok(())
    }
}
