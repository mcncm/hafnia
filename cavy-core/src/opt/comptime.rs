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
//!
//! TODO There is a *lot* of allocation happening in here. It might be faster to
//! allocate a single `Vec` once for each local, instead of building trees.
//!
//! TODO Forbid erasure of const I/O. This might be a complicated analysis.
//!
//! TODO Incredibly, constant propagation currently only runs through the *first
//! block*. Somehow I didn't finish this. Note that the problem is more
//! complicated with branches, because you much correctly merge your knowledge
//! at each of the parent branches. Traditionally this optimization is done in
//! SSA, with phi-functions at each merge point. I think we can do something
//! completely *equivalent*

use std::collections::{hash_map::Entry, HashMap};

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
    let blk = &mut gr[blk];
    for stmt in blk.stmts.iter_mut() {
        simpl_stmt(stmt, interp);
    }

    match &mut blk.kind {
        BlockKind::Goto(_) => {}
        BlockKind::Switch { cond, ref mut blks } => match interp.env.get(cond) {
            Some(&Value::Bool(false)) => blk.kind = BlockKind::Goto(blks[0]),
            Some(&Value::Bool(true)) => blk.kind = BlockKind::Goto(blks[1]),
            _ => {}
        },
        BlockKind::Call(call) => {
            // Replace args with compile-time evaluated ones
            for arg in call.args.iter_mut() {
                if let Operand::Copy(place) | Operand::Move(place) = arg {
                    if let Some(c) = interp.env.get(&place) {
                        *arg = Operand::Const(c.clone());
                    }
                }
            }

            // This is a pretty critical missing component. For now we're not
            // going to do any compile-time evaluation even of purely classical
            // functions.
            simpl_block(call.blk, gr, interp);
        }
        crate::mir::BlockKind::Ret => {}
    }
}

fn simpl_stmt(stmt: &mut Stmt, interp: &mut Interpreter) {
    match &mut stmt.kind {
        StmtKind::Assn(place, ref mut rhs) => {
            if let Evaluated::Yes = interp.exec(place, rhs) {
                stmt.kind = StmtKind::Nop;
            }
        }
        StmtKind::Assert(_) => {}
        StmtKind::Drop(_) => {}
        StmtKind::Io(_) => {}
        StmtKind::Nop => {}
    }
}

/// This little enum is just here to be explicit about the meaning of the
/// boolean returned by `Interpreter::exec`.
enum Evaluated {
    Yes,
    No,
}

struct Environment {
    backing_store: HashMap<LocalId, Value>,
}

impl Environment {
    fn new() -> Self {
        Self {
            backing_store: HashMap::new(),
        }
    }

    fn get(&self, place: &Place) -> Option<&Value> {
        self.backing_store
            .get(&place.root)
            .and_then(|value| value.follow(&place.path))
    }

    fn insert(&mut self, place: &Place, value: Value) {
        match self.backing_store.entry(place.root) {
            Entry::Occupied(mut e) => {
                let old = e.get_mut().follow_mut(&place.path);
                *old = value;
            }
            Entry::Vacant(e) => {
                let mut root = Value::Unit;
                let slot = root.follow_mut(&place.path);
                *slot = value;
                e.insert(root);
            }
        };
    }
}

struct Interpreter {
    env: Environment,
}

/// A graph-local interpreter for classical computations
impl Interpreter {
    fn new() -> Self {
        Self {
            env: Environment::new(),
        }
    }

    fn operand_value(&self, operand: &Operand) -> Option<Value> {
        match operand {
            Operand::Const(v) => Some(v.clone()),
            Operand::Copy(place) | Operand::Move(place) => self.env.get(place).cloned(),
        }
    }

    /// If possible, evaluate the right-hand side, and store the result in the
    /// left-hand-side. It's possible to evaluate the rhs iff everything
    /// appearing in it is const.
    fn exec(&mut self, place: &Place, rhs: &mut Rvalue) -> Evaluated {
        use Operand::*;
        match &mut rhs.data {
            // We need to special-case the `Swap` operator, because it
            // doesn't require both of its operands to be evaluated
            RvalueKind::BinOp(BinOp::Swap, u, v) => match (&u, &v) {
                (Const(c), Move(place)) | (Move(place), Const(c)) => {
                    self.env.insert(place, c.clone());
                    Evaluated::Yes
                }
                _ => Evaluated::No,
            },

            RvalueKind::BinOp(op, u, v) => {
                if let (Some(u), Some(v)) = (self.operand_value(u), self.operand_value(v)) {
                    match op {
                        BinOp::Plus => self.env.insert(place, self.eval_plus(u, v)),
                        BinOp::Times => self.env.insert(place, self.eval_times(u, v)),
                        BinOp::Equal => self.env.insert(place, self.eval_equal(u, v)),
                        BinOp::Nequal => {
                            self.env.insert(place, self.eval_not(self.eval_equal(u, v)))
                        }
                        // Previously special-cased
                        BinOp::Swap => unreachable!(),
                        _ => return Evaluated::No,
                    };
                    return Evaluated::Yes;
                }
                Evaluated::No
            }

            RvalueKind::UnOp(UnOp::Linear, Copy(rplace))
            | RvalueKind::UnOp(UnOp::Linear, Move(rplace)) => {
                if let Some(c) = self.env.get(rplace) {
                    rhs.data = RvalueKind::UnOp(UnOp::Linear, Const(c.clone()));
                }
                Evaluated::No
            }

            RvalueKind::UnOp(UnOp::Linear, Const(_)) => unreachable!(),

            RvalueKind::UnOp(UnOp::Not, Copy(rplace))
            | RvalueKind::UnOp(UnOp::Not, Move(rplace)) => {
                if let Some(c) = self.env.get(rplace).cloned() {
                    self.env.insert(place, self.eval_not(c));
                    return Evaluated::Yes;
                }
                Evaluated::No
            }

            RvalueKind::UnOp(UnOp::Not, Const(_)) => unreachable!(),

            RvalueKind::UnOp(UnOp::Split, _) => Evaluated::No,

            RvalueKind::UnOp(UnOp::Delin, _) => Evaluated::No,

            RvalueKind::UnOp(UnOp::Minus, _) => todo!(),

            RvalueKind::Use(val) => match val {
                Move(rplace) | Copy(rplace) => {
                    if let Some(c) = self.env.get(rplace).cloned() {
                        self.env.insert(place, c);
                        return Evaluated::Yes;
                    }
                    Evaluated::No
                }
                Const(c) => {
                    self.env.insert(place, c.clone());
                    Evaluated::Yes
                }
            },
            // NOTE: is this always correct?
            RvalueKind::Ref(_, rplace) => {
                if let Some(c) = self.env.get(rplace).cloned() {
                    self.env.insert(place, c);
                    return Evaluated::Yes;
                }
                Evaluated::No
            }
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
