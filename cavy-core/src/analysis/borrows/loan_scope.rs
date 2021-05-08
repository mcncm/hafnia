//! This analysis computes the scope of each `Loan`, using the analysis outlined
//! in [Borrow checker phase
//! 1](https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md#borrow-checker-phase-1-computing-loans-in-scope)

use bitvec::access::BitSafeUsize;

use crate::{bitset, store::BitSet};

use super::{
    super::dataflow::{DataflowAnalysis, Forward, Lattice, Statementwise, StmtStates},
    ascription::{AscriptionStore, Loan},
    regions::{LifetimeStore, RegionInf},
    *,
};

pub use super::ascription::LoanId;

bitset! { LocalLoans(LoanId) }

pub fn loan_scopes(regions: &RegionInf, context: &DataflowCtx) -> StmtStates<LocalLoans> {
    let loan_ana = LiveLoanAnalysis::new(&regions);
    DataflowRunner::new(loan_ana, &context).run().stmt_states
}

impl Lattice for LocalLoans {
    fn join(self, other: Self) -> Self {
        self | other
    }
}

type BitR<'b> = BitRef<'b, bitvec::ptr::Mut, Lsb0, BitSafeUsize>;

pub struct LiveLoanAnalysis<'a> {
    /// The number of loans in the program
    size: usize,
    ascriptions: &'a AscriptionStore<'a>,
    lifetimes: &'a LifetimeStore,
}

impl<'a> LiveLoanAnalysis<'a> {
    pub fn new(regions: &'a RegionInf) -> Self {
        let ascriptions = &regions.ascriptions;
        Self {
            size: ascriptions.loans.len(),
            ascriptions,
            lifetimes: &regions.lifetimes,
        }
    }

    fn foreach_loan<F>(&self, state: &mut LocalLoans, mut f: F)
    where
        F: FnMut(&Loan, BitR),
    {
        // Ach, let's just use the richer API from `bitvec`
        for (ln, bit) in state
            .0
            .as_mut_bitslice()
            .iter_mut()
            .enumerate()
            // look at the memembers of the set
            .filter(|(_, bit)| **bit)
        {
            let loan = &self.ascriptions.loans[LoanId::from(ln as u32)];
            f(loan, bit);
        }
    }

    fn kill_region_not_in_scope(&self, loan: &Loan, mut bit: BitR, pt: &GraphPt) {
        if !self.lifetimes[loan.ascr.lt].contains(&pt) {
            *bit = false;
            return;
        }
    }

    fn kill_lhs_prefix(&self, lhs: &Place, loan: &Loan, mut bit: BitR) {
        if lhs.is_prefix(&loan.place) {
            *bit = false;
        }
    }
}

impl<'a> DataflowAnalysis<Forward, Statementwise> for LiveLoanAnalysis<'a> {
    type Domain = LocalLoans;

    fn bottom(&self) -> Self::Domain {
        Self::Domain::empty(self.size)
    }

    /// Per the RFC, we apply the rules:
    ///
    /// + Kill loans that don't have the point in their region. We've stored an
    ///   `LtId` in each loan, so that's no problem.
    ///
    /// + Generate the loan at the borrow statement it came from. We've stored
    ///   our `LtId`s in a point-indexed map. No problem.
    ///
    /// + Kill loans that have the lhs as a prefix. This is a *slight* problem.
    ///   Our loans should probably be in some kind of prefix tree of pseudotype
    ///   `Tree<Vec<Loan>>`. That would be really "correct." In fact, we could
    ///   fuse the ascription tree with the loan tree (the tree builder is
    ///   *already* collecting that data), and search over *that* starting from
    ///   the lhs.
    ///
    ///   I'm not going to do that, though. I'm cloning `Place`s into every
    ///   `Loan` and checking if the lhs is a prefix of the `Place` in every
    ///   live `Loan.` This isn't "right," but I can get it done much faster and
    ///   have this working.
    fn transfer_stmt(&self, state: &mut Self::Domain, stmt: &Stmt, pt: GraphPt) {
        self.foreach_loan(state, |loan, mut bit| {
            // Kill loans whose regions are not in the point.
            if !self.lifetimes[loan.ascr.lt].contains(&pt) {
                *bit = false;
                return;
            }

            // Kill loans that have the lhs as a prefix.
            if let StmtKind::Assn(lhs, _) = &stmt.kind {
                self.kill_lhs_prefix(lhs, loan, bit);
            }
        });

        // Generate the loan at the borrow statement it came from.
        if let Some(ln) = self.ascriptions.refs.get(&pt) {
            state.set(*ln, true);
        }
    }

    fn transfer_block(&self, state: &mut Self::Domain, block: &BlockKind, pt: GraphPt) {
        self.foreach_loan(state, |loan, mut bit| {
            // Kill loans whose regions are not in the point.
            if !self.lifetimes[loan.ascr.lt].contains(&pt) {
                *bit = false;
                return;
            }

            // Kill loans that have the lhs as a prefix.
            if let BlockKind::Call(call) = block {
                self.kill_lhs_prefix(&call.ret, loan, bit);
            }
        });
    }
}
