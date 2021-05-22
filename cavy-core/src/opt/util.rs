use std::{collections::HashMap, iter::Enumerate};

use crate::{mir::*, store::BitSet};

pub trait Interleave<T>
where
    Self: Iterator<Item = T>,
{
    fn interleave<J>(self, other: J) -> Interleaver<Self, J, T>
    where
        J: Iterator<Item = (usize, T)>,
        Self: Sized,
    {
        Interleaver::new(self, other)
    }
}

pub struct Interleaver<I, J, T>
where
    I: Iterator<Item = T>,
    J: Iterator<Item = (usize, T)>,
{
    fst: Enumerate<I>,
    snd: J,
    fst_next: Option<(usize, T)>,
    snd_next: Option<(usize, T)>,
}

impl<I, J, T> Interleaver<I, J, T>
where
    I: Iterator<Item = T>,
    J: Iterator<Item = (usize, T)>,
{
    fn new(fst: I, mut snd: J) -> Self {
        let mut fst = fst.enumerate();
        let fst_next = fst.next();
        let snd_next = snd.next();
        Self {
            fst,
            snd,
            fst_next,
            snd_next,
        }
    }

    fn next_fst(&mut self) -> Option<T> {
        let next = std::mem::replace(&mut self.fst_next, self.fst.next());
        Some(next.unwrap().1)
    }

    fn next_snd(&mut self) -> Option<T> {
        let next = std::mem::replace(&mut self.snd_next, self.snd.next());
        Some(next.unwrap().1)
    }
}

impl<I, J, T> Iterator for Interleaver<I, J, T>
where
    I: Iterator<Item = T>,
    J: Iterator<Item = (usize, T)>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match (&mut self.fst_next, &mut self.snd_next) {
            // There must be a better way with library functions, without having
            // to unwrap and rewrap like this
            (Some(fst), Some(snd)) => {
                if fst.0 == snd.0 {
                    self.next_fst()
                } else {
                    self.next_snd()
                }
            }
            (Some(_), _) => self.next_fst(),
            (_, Some(_)) => self.next_snd(),
            _ => None,
        }
    }
}

/// Do something to every `Place` in the graph
pub fn foreach_place<F>(gr: &mut Graph, mut f: F)
where
    F: FnMut(&mut Place),
{
    for block in gr.iter_mut() {
        // Everything in all the statements
        for stmt in block.stmts.iter_mut() {
            match &mut stmt.kind {
                StmtKind::Assn(lhs, rv) => {
                    f(lhs);
                    for place in rv.places_mut() {
                        f(place);
                    }
                }
                StmtKind::Assert(place) | StmtKind::Drop(place) => {
                    f(place);
                }
                StmtKind::Io(io) => match io {
                    IoStmtKind::In => {}
                    IoStmtKind::Out { place, .. } => f(place),
                },
                StmtKind::Nop => {}
            }
        }

        // ...And everything in all the block tails
        match &mut block.kind {
            BlockKind::Goto(_) => {}
            BlockKind::Switch(switch) => {
                f(&mut switch.cond);
            }
            BlockKind::Call(call) => {
                f(&mut call.ret);
                for arg in call.args.iter_mut() {
                    if let Some(place) = arg.place_mut() {
                        f(place);
                    }
                }
            }
            BlockKind::Ret => {}
        }
    }
}

/// Do something to every `BlockKind` in the graph
pub fn foreach_block<F>(gr: &mut Graph, mut f: F)
where
    F: FnMut(&mut BasicBlock),
{
    for block in gr.iter_mut() {
        f(block)
    }
}

pub fn retain_blocks<F>(gr: &mut Graph, mut f: F)
where
    F: FnMut(BlockId, &BasicBlock) -> bool,
{
    let mut new_blks = HashMap::<BlockId, BlockId>::new();
    let mut ctr = crate::store::Counter::new();
    gr.get_blocks_mut().idx_retain(|idx, block| {
        f(idx, block) && {
            new_blks.insert(idx, ctr.next().unwrap());
            true
        }
    });
    // Renumber all the `BlockId`s appearing in the graph
    foreach_block(gr, |block| {
        let blks = match &mut block.kind {
            BlockKind::Goto(blk) => std::slice::from_mut(blk),
            BlockKind::Switch(switch) => switch.blks.as_mut_slice(),
            BlockKind::Call(call) => std::slice::from_mut(&mut call.blk),
            BlockKind::Ret => &mut [],
        };
        for blk in blks {
            match new_blks.get(&*blk) {
                Some(new) => {
                    *blk = *new;
                }
                None => unreachable!("no removed block should still be accessible"),
            }
        }
    });
}
