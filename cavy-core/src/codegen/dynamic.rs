use std::{collections::VecDeque, ops::RangeFrom};

use crate::{
    circuit::Gate,
    mir::{BlockId, BlockKind, Graph, Mir, Place, Rvalue, Stmt, StmtKind},
    session::Config,
};

struct Allocator<T, I>
where
    I: Iterator<Item = T>,
{
    /// Unused items
    fresh: I,
    /// A clean free set that can be reallocated immediately
    clean: Vec<T>,
    /// A dirty free set that should be scheduled for reset
    dirty: VecDeque<T>,
}

impl<T, I> Allocator<T, I>
where
    I: Iterator<Item = T>,
{
    fn new(items: I) -> Self {
        Self {
            fresh: items,
            clean: Vec::new(),
            dirty: VecDeque::new(),
        }
    }

    fn alloc_one(&mut self) -> Option<T> {
        self.clean
            .pop()
            .or_else(|| self.dirty.pop_front().or_else(|| self.fresh.next()))
    }

    fn alloc(&mut self, n: usize) -> Vec<T> {
        std::iter::from_fn(|| self.alloc_one()).take(n).collect()
    }

    fn free_clean(&mut self, item: T) {
        self.clean.push(item);
    }

    fn free_dirty(&mut self, item: T) {
        self.dirty.push_back(item);
    }
}

struct BitAllocator {
    class: Allocator<usize, RangeFrom<usize>>,
    quant: Allocator<usize, RangeFrom<usize>>,
}

impl BitAllocator {
    fn new() -> Self {
        Self {
            class: Allocator::new(0..),
            quant: Allocator::new(0..),
        }
    }
}

pub struct InterpreterState<'m> {
    gr: &'m Graph,
    next_candidates: Vec<BlockId>,
}

impl<'m> InterpreterState<'m> {
    fn new(gr: &'m Graph) -> Self {
        Self {
            gr,
            next_candidates: vec![],
        }
    }
}

pub struct Environment {}

impl Environment {
    fn new() -> Self {
        Self {}
    }

    fn insert(&mut self, _place: &Place, _value: ()) {
        todo!()
    }
}

pub struct Interpreter<'m> {
    mir: &'m Mir,
    alloc: BitAllocator,
    gate_buf: Vec<Gate>,
    st: InterpreterState<'m>,
    env: Environment,
    env_stack: Vec<Environment>,
}

impl<'m> Interpreter<'m> {
    fn new(mir: &'m Mir) -> Self {
        let entry_point = mir.entry_point.unwrap();
        let gr = &mir.graphs[entry_point];
        Self {
            alloc: BitAllocator::new(),
            gate_buf: Vec::new(),
            env: Environment::new(),
            env_stack: Vec::new(),
            st: InterpreterState::new(gr),
            mir,
        }
    }

    fn exec(mut self) -> Vec<Gate> {
        let mut block_candidates = vec![self.st.gr.entry_block];
        while !block_candidates.is_empty() {
            for blk in block_candidates.drain(0..) {
                self.exec_block(blk);
            }
            std::mem::swap(&mut block_candidates, &mut self.st.next_candidates);
        }
        self.gate_buf
    }

    fn push_stack(&mut self) {
        self.env_stack
            .push(std::mem::replace(&mut self.env, Environment::new()));
    }

    fn exec_block(&mut self, blk: BlockId) {
        let blk = &self.st.gr[blk];
        for stmt in &blk.stmts {
            self.exec_stmt(stmt);
        }
        self.terminate(&blk.kind);
    }

    fn exec_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Assn(place, rvalue) => self.exec_assn(&place, &rvalue),
            StmtKind::Assert(_place) => {
                // See, this is why we need these analysis things. It's really
                // pretty hard to say whether something has been asserted from
                // local data alone, if you have any join points.
                todo!();
            }
            StmtKind::Io(_io) => {
                todo!();
            }
            StmtKind::Nop => {}
        }
    }

    fn exec_assn(&mut self, place: &Place, rvalue: &Rvalue) {
        let value = self.compute(rvalue);
        self.env.insert(place, value);
    }

    fn compute(&mut self, _rvalue: &Rvalue) -> () {
        todo!();
    }

    fn terminate(&mut self, _kind: &BlockKind) {
        todo!();
    }
}
