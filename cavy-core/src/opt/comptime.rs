//! In Cavy, all classical values that can be computed at compile time are so
//! evalutated. We might call this "constant propagatation" or "compile-time
//! evaluation" in different places; here, the two will be synonymous.
//!
//! Which are the classical values that can be computed at compile time? In
//! short, any that are deterministic and not downstream of any measurement
//! operator. Since there is currently no primitive classical randomness in the
//! language, this means exactly that classical computation between the entry
//! point and the first linearization operator.
//!
//! NOTE This currently works under the assumption that there are no infinite
//! loops or recursion. It's one of the points of failure when that eventually
//! changes.

use std::collections::HashMap;

use crate::{context::Context, mir::*, values::Value};

/// Main entry point for compile-time evaluation. This takes the form of a Mir
/// optimization, which is currently a function taking a mutable reference to
/// the Mir. In the future, multiple optimizations may be handled by some common
/// framework, similar to the dataflow analyses.
///
/// For now, even *this* optimization is intraprocedural. That *must* change.
pub fn propagate_consts(mir: &mut Mir, _ctx: &Context) {
    for gr in mir.graphs.iter_mut() {
        simpl_graph(gr);
    }
}

fn simpl_graph(gr: &mut Graph) {
    let mut interp = Interpreter::new();
    simpl_block(gr.entry_block, gr, &mut interp);
}

fn simpl_block(blk: BlockId, gr: &mut Graph, interp: &mut Interpreter) {
    let blk = &mut gr.blocks[blk];
    for stmt in blk.stmts.iter_mut() {
        simpl_stmt(stmt, interp);
    }

    match &mut blk.kind {
        BlockKind::Goto(_) => {}
        BlockKind::Switch { cond, ref mut blks } => match interp.value_of(cond) {
            Some(&Value::Bool(false)) => blk.kind = BlockKind::Goto(blks[0]),
            Some(&Value::Bool(true)) => blk.kind = BlockKind::Goto(blks[1]),
            _ => {}
        },
        BlockKind::Call {
            callee: _,
            span: _,
            ref mut args,
            blk,
        } => {
            // Replace args with compile-time evaluated ones
            for arg in args.iter_mut() {
                if let Operand::Copy(loc) | Operand::Move(loc) = arg {
                    if let Some(c) = interp.value_of(loc) {
                        *arg = Operand::Const(c.clone());
                    }
                }
            }

            // This is a pretty critical missing component. For now we're not
            // going to do any compile-time evaluation even of purely classical
            // functions.
            simpl_block(*blk, gr, interp);
        }
        crate::mir::BlockKind::Ret => {}
    }
}

fn simpl_stmt(stmt: &mut Stmt, interp: &mut Interpreter) {
    match &mut stmt.kind {
        StmtKind::Assn(place, ref mut rhs) => {
            if let Evaluated::Yes = interp.exec(*place, rhs) {
                stmt.kind = StmtKind::Nop;
            }
        }
        StmtKind::Nop => return,
    }
}

/// This little enum is just here to be explicit about the meaning of the
/// boolean returned by `Interpreter::exec`.
enum Evaluated {
    Yes,
    No,
}

struct Interpreter {
    env: HashMap<LocalId, Value>,
}

/// A graph-local interpreter for classical computations
impl Interpreter {
    fn new() -> Self {
        Self {
            env: HashMap::new(),
        }
    }

    fn value_of(&self, local: &LocalId) -> Option<&Value> {
        self.env.get(&local)
    }

    fn operand_value(&self, operand: &Operand) -> Option<Value> {
        match operand {
            Operand::Const(v) => Some(v.clone()),
            Operand::Copy(loc) | Operand::Move(loc) => self.env.get(loc).cloned(),
        }
    }

    /// If possible, evaluate the right-hand side, and store the result in the
    /// left-hand-side. It's possible to evaluate the rhs iff everything
    /// appearing in it is const.
    fn exec(&mut self, place: LocalId, rhs: &mut Rvalue) -> Evaluated {
        use Operand::*;
        match &mut rhs.data {
            RvalueKind::BinOp(op, u, v) => {
                if let (Some(u), Some(v)) = (self.operand_value(u), self.operand_value(v)) {
                    match op {
                        BinOp::Plus => self.env.insert(place, self.eval_plus(u, v)),
                        BinOp::Times => self.env.insert(place, self.eval_times(u, v)),
                        BinOp::Equal => self.env.insert(place, self.eval_equal(u, v)),
                        BinOp::Nequal => {
                            self.env.insert(place, self.eval_not(self.eval_equal(u, v)))
                        }
                        _ => todo!(),
                    };
                    return Evaluated::Yes;
                }
                Evaluated::No
            }

            RvalueKind::UnOp(UnOp::Linear, Copy(v)) | RvalueKind::UnOp(UnOp::Linear, Move(v)) => {
                if let Some(c) = self.env.get(v) {
                    rhs.data = RvalueKind::UnOp(UnOp::Linear, Const(c.clone()));
                }
                Evaluated::No
            }

            RvalueKind::UnOp(UnOp::Not, Copy(v)) | RvalueKind::UnOp(UnOp::Not, Move(v)) => {
                if let Some(c) = self.env.get(v).cloned() {
                    self.env.insert(place, self.eval_not(c));
                    return Evaluated::Yes;
                }
                Evaluated::No
            }

            RvalueKind::UnOp(_, _) => todo!(),

            RvalueKind::Use(val) => match val {
                Move(v) | Copy(v) => {
                    if let Some(c) = self.env.get(v).cloned() {
                        self.env.insert(place, c.clone());
                        return Evaluated::Yes;
                    }
                    Evaluated::No
                }
                Const(c) => {
                    self.env.insert(place, c.clone());
                    return Evaluated::Yes;
                }
            },
        }
    }

    fn eval_not(&self, x: Value) -> Value {
        match x {
            Value::Bool(b) => Value::Bool(!b),
            Value::U8(n) => Value::U8(!n),
            Value::U16(n) => Value::U16(!n),
            Value::U32(n) => Value::U32(!n),
            // Forbidden by type checker
            _ => unreachable!(),
        }
    }

    fn eval_plus(&self, n: Value, m: Value) -> Value {
        match (n, m) {
            (Value::U8(n), Value::U8(m)) => Value::U8(n + m),
            (Value::U16(n), Value::U16(m)) => Value::U16(n + m),
            (Value::U32(n), Value::U32(m)) => Value::U32(n + m),
            // Forbidden by type checker
            _ => unreachable!(),
        }
    }

    fn eval_times(&self, n: Value, m: Value) -> Value {
        match (n, m) {
            (Value::U8(n), Value::U8(m)) => Value::U8(n * m),
            (Value::U16(n), Value::U16(m)) => Value::U16(n * m),
            (Value::U32(n), Value::U32(m)) => Value::U32(n * m),
            // Forbidden by type checker
            _ => unreachable!(),
        }
    }

    fn eval_equal(&self, u: Value, v: Value) -> Value {
        if u == v {
            Value::Bool(true)
        } else {
            Value::Bool(false)
        }
    }
}
