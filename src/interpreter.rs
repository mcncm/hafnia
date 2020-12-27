use crate::alloc::QubitAllocator;
use crate::arch::Arch;
use crate::ast::{
    Block, Expr, ExprKind, Ident, Item, ItemKind, LValue, LValueKind, Stmt, StmtKind,
};
use crate::environment::{Environment, Key, Moveable, Nameable};
use crate::errors::ErrorBuf;
use crate::parser::ParseError;
use crate::qram::Qram;
use crate::scanner::{ScanError, Scanner};
use crate::source::Span;
use crate::token::{Lexeme, Token};
use crate::types::{self, Type};
use crate::{
    circuit::{Circuit, Gate, Qubit},
    functions::{Func, UserFunc},
    values::{self, Value},
};

use std::{
    collections::{HashMap, HashSet},
    fmt, mem,
    rc::Rc,
};

#[derive(Debug)]
pub struct InterpreterError {
    msg: String,
    loc: Option<Span>,
}

impl fmt::Display for InterpreterError {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.loc {
            Some(loc) => {
                write!(f, "Interpreter error at {}: {}",
                       loc, self.msg)
            } ,
            None => {
                write!(f, "Interpreter error: {}", self.msg)
            }
        }
    }
}

impl std::error::Error for InterpreterError {}

pub struct Interpreter<'a> {
    pub env: Environment,
    pub circuit: Circuit,
    pub qram: Option<Qram>,
    qubit_allocator: QubitAllocator<'a>,
    arch: &'a Arch,
    // This flag indicates whether code generation is currently covariant or
    // contravariant. It’s an implementation detail, and I’m not sure I like the
    // design of branching on a flag. I’m sure to think about this more, and
    // this detail may not be permanent.
    contra: bool,
    // Another implementation detail of contravariant evaluation. This stack is
    // allocated here so that lives long enough to push into it in a
    // contravariant context.
    contra_stack: Vec<Gate>,
}

impl<'a> Interpreter<'a> {
    pub fn new(arch: &'a Arch) -> Self {
        let mut qubit_allocator = QubitAllocator::new(&arch);
        let mut qram = None;
        if arch.qram_size > 0 {
            qram = Some(Qram::new(&mut qubit_allocator, arch.qram_size));
        }
        Self {
            env: Environment::base(),
            circuit: Circuit::new(),
            qubit_allocator,
            qram,
            arch: &arch,
            contra: false,
            contra_stack: vec![],
        }
    }

    /////////////////////////
    // Statement execution //
    /////////////////////////

    #[rustfmt::skip]
    pub fn execute(&mut self, stmt: &Stmt) -> Result<(), ErrorBuf> {
        use crate::ast::Expr;
        use StmtKind::*;
        match &stmt.kind {
            Print(expr) => {
                println!("{}", self.evaluate(&expr)?);
                Ok(())
            },
            Local { lhs, rhs, .. } => self.exec_local(lhs, rhs),
            Item(item) => self.exec_item(item),
            Expr(expr) | ExprSemi(expr) => {
                self.evaluate(expr)?;
                Ok(())
            }
        }
    }

    fn exec_item(&mut self, item: &Item) -> Result<(), ErrorBuf> {
        match &item.kind {
            ItemKind::Fn {
                name, params, body, ..
            } => self.exec_fn(name, params, body),
        }
    }

    /// Create a local binnnding
    #[rustfmt::skip]
    fn exec_local(&mut self, lhs: &LValue, rhs: &Expr) -> Result<(), ErrorBuf> {
        let rhs = self.evaluate(rhs)?;
        let bindings = self.destruct_bind(lhs, &rhs)?;
        for (name, val) in bindings {
            self.env.insert(name, val);
        }
        Ok(())
    }

    /// Recursively build a set of bindings from a valid lvalue and rvalue.
    fn destruct_bind(
        &mut self,
        lhs: &LValue,
        rhs: &Value,
    ) -> Result<HashMap<String, Nameable>, ErrorBuf> {
        Ok(self.destruct_bind_inner(lhs, rhs)?.into_iter().collect())
    }

    /// In the recursive inner subroutine, we delegate the bindings to a Vec,
    /// which should be a bit faster than a HashMap, as well as easier to work
    /// with.
    ///
    /// TODO There is not yet any checking for uniqueness! I’ve left this
    /// because it should perhaps be done in an earlier pass.
    fn destruct_bind_inner(
        &mut self,
        lhs: &LValue,
        rhs: &Value,
    ) -> Result<Vec<(String, Nameable)>, ErrorBuf> {
        let mut bindings = vec![];

        match (&lhs.kind, &rhs) {
            (LValueKind::Ident(ident), _) => {
                bindings.push((ident.name.clone(), Nameable::Value(rhs.clone())));
            }
            (LValueKind::Tuple(binders), Value::Array(values))
            | (LValueKind::Tuple(binders), Value::Tuple(values)) => {
                if binders.len() != values.len() {
                    todo!(); // Should be an error
                }
                for (binder, value) in binders.iter().zip(values.iter()) {
                    bindings.append(&mut self.destruct_bind_inner(binder, value)?);
                }
            }
            _ => todo!(),
        }
        Ok(bindings)
    }

    /// Calling this function is how Cavy functions are defined. This has some
    /// weird consequences. One is that in nested functions, or functions
    /// defined in loops, they are redefined every time they are encountered. I
    /// think function definitions should maybe be resolved at some *earlier*
    /// time, before evaluation.
    fn exec_fn(
        &mut self,
        name: &str,
        params: &[(String, Type)],
        body: &Block,
    ) -> Result<(), ErrorBuf> {
        let params = params
            .iter()
            .map(|(param, _)| param.clone())
            .collect::<Vec<String>>();
        let body = Box::new(body.clone());

        let func = UserFunc {
            params,
            body,
            doc: None,
        };

        self.env
            .insert(name.to_string(), Nameable::Func(Rc::new(func)));

        Ok(())
    }

    fn eval_if(
        &mut self,
        cond: &Expr,
        then_branch: &Block,
        else_branch: &Option<Box<Block>>,
    ) -> Result<Value, ErrorBuf> {
        // Note that `self` is passed as a parameter to the closure, rather than
        // captured from the environment. The latter would violate the borrow
        // checker rules by making a second mutable borrow.

        // NOTE This may not be very idiomatic, and it’s not unlikely that a
        // future refactoring will replace this pattern entirely.
        self.coevaluate(cond, &mut |self_, cond_val| {
            self_.eval_if_inner(&cond_val, then_branch, else_branch)
        })
    }

    fn eval_if_inner(
        &mut self,
        cond_val: &Value,
        then_branch: &Block,
        else_branch: &Option<Box<Block>>,
    ) -> Result<Value, ErrorBuf> {
        match cond_val {
            // FIXME This is less than half of an implementation!
            Value::Q_Bool(u) => {
                // FIXME This is far from a proper and complete solution to the
                // evaluation of If expressions. For one thing, they’re
                // dynamically typed: the return values are not guaranteed to be
                // the same type, and it might only fail contingently at
                // runtime. Also, there isn’t as strong of a distinction between
                // If statements and If expressions as feels appropriate.
                match &else_branch {
                    None => {
                        let controls = vec![*u];
                        self.eval_block(then_branch, None, controls)?;
                        Ok(Value::Unit)
                    }
                    _ => {
                        todo!();
                    }
                }
            }
            Value::Bool(_) => {
                if cond_val.is_truthy() {
                    self.eval_block(then_branch, None, vec![])
                } else if let Some(else_branch) = else_branch {
                    self.eval_block(else_branch, None, vec![])
                } else {
                    Ok(Value::Unit)
                }
            }
            _ => panic!("Violated a typing invariant"),
        }
    }

    fn eval_for(&mut self, bind: &LValue, iter: &Expr, body: &Block) -> Result<Value, ErrorBuf> {
        self.coevaluate(iter, &mut |self_, iter_val| {
            self_.eval_for_inner(bind, &iter_val, body)
        })?;
        Ok(Value::Unit)
    }

    // Yes, this one is called `eval` because the blocks are actually
    // expressions; we're just dumping the return values.
    fn eval_for_inner(
        &mut self,
        bind: &LValue,
        iter: &Value,
        body: &Block,
    ) -> Result<Value, ErrorBuf> {
        use Lexeme::Ident;
        // Unwrap the data for now. I suspect we *don’t* want to be iterating over
        // tuples, for instance.
        let iter = match iter {
            Value::Array(data) => data,
            _ => panic!(),
        };

        for item in iter.iter() {
            let bindings = self.destruct_bind(bind, item)?;
            self.eval_block(&body, Some(bindings), vec![])?;
        }
        Ok(Value::Unit)
    }

    fn eval_let(&mut self, lhs: &LValue, rhs: &Expr, body: &Block) -> Result<Value, ErrorBuf> {
        // Note that `self` is passed as a parameter to the closure, rather than
        // captured from the environment. The latter would violate the borrow
        // checker rules by making a second mutable borrow.
        //
        // NOTE This may not be very idiomatic, and it’s not unlikely that a
        // future refactoring will replace this pattern entirely.
        self.coevaluate(rhs, &mut |self_, rhs_val| {
            self_.eval_let_inner(lhs, &rhs_val, body)
        })
    }

    fn eval_let_inner(
        &mut self,
        lhs: &LValue,
        rhs: &Value,
        body: &Block,
    ) -> Result<Value, ErrorBuf> {
        use ExprKind::Block;
        let bindings = self.destruct_bind(lhs, rhs)?;
        self.eval_block(&body, Some(bindings), vec![])
    }

    ///////////////////////////
    // Expression evaluation //
    ///////////////////////////

    /// Evaluate an expression
    pub fn evaluate(&mut self, expr: &Expr) -> Result<Value, ErrorBuf> {
        use ExprKind::*;
        match &expr.kind {
            BinOp { left, op, right } => self.eval_binop(left, op, right),
            UnOp { op, right } => self.eval_unop(op, right),
            Literal(literal) => self.eval_literal(literal),
            Ident(ident) => self.eval_ident(ident),
            Tuple(items) => self.eval_tuple(items),
            IntArr { item, reps } => self.eval_int_arr(item, reps),
            ExtArr(items) => self.eval_ext_arr(items),
            If {
                cond,
                then_branch,
                else_branch,
            } => self.eval_if(cond, then_branch, else_branch),
            For { bind, iter, body } => self.eval_for(bind, iter, body),
            Let { lhs, rhs, body } => self.eval_let(lhs, rhs, body),
            Block(block) => self.eval_block(block, None, vec![]),
            Call { callee, args, .. } => self.eval_call(callee, args),
            Index { head, index, .. } => self.eval_index(head, index),
        }
    }

    /// NOTE This function is only public because it’s used by user-defined
    /// functions. It’s not clearly something that *should* be exposed as part
    /// of the compiler API.
    pub fn eval_block(
        &mut self,
        block: &Block,
        bindings: Option<HashMap<Key, Nameable>>,
        controls: Vec<Qubit>,
    ) -> Result<Value, ErrorBuf> {
        self.env.open_scope(bindings, controls);
        let val = self.eval_block_inner(&block.stmts);
        self.env.close_scope();
        val
    }

    fn eval_block_inner(&mut self, stmts: &[Stmt]) -> Result<Value, ErrorBuf> {
        let (last, rest) = match stmts.split_last() {
            Some((last, rest)) => (last, rest),
            None => {
                return Ok(Value::Unit);
            }
        };

        for stmt in rest.iter() {
            self.execute(stmt)?;
        }

        match &last.kind {
            StmtKind::Expr(expr) => {
                let value = self.evaluate(expr)?;
                Ok(value)
            }
            _ => {
                self.execute(last)?;
                Ok(Value::Unit)
            }
        }
    }

    fn eval_literal(&self, literal: &Token) -> Result<Value, ErrorBuf> {
        use crate::token::Lexeme;
        // TODO
        match literal.lexeme {
            Lexeme::Nat(nat) => Ok(Value::U32(nat)),
            Lexeme::True => Ok(Value::Bool(true)),
            Lexeme::False => Ok(Value::Bool(false)),
            _ => todo!(),
        }
    }

    fn eval_ident(&mut self, ident: &Ident) -> Result<Value, ErrorBuf> {
        use crate::token::Lexeme;
        use Moveable::*;
        let name = &ident.name;
        // About this unwrap: we will at some point in the (hopefully
        // near) future track whether this operation is safe statically,
        // and always know when there is a value in the environment.
        match self.env.get(&name) {
            Some(There(Nameable::Value(val))) => Ok(val),
            Some(Moved) => {
                let err = InterpreterError {
                    msg: format!("the variable `{}` has been moved.", name),
                    loc: Some(ident.span.clone()),
                };
                Err(ErrorBuf(vec![Box::new(err)]))
            }
            None => {
                let err = InterpreterError {
                    msg: format!("the name `{}` is unbound.", name),
                    loc: Some(ident.span.clone()),
                };
                Err(ErrorBuf(vec![Box::new(err)]))
            }
            // In the near-term this should just be an error; in the
            // long term, there should be first-class functions.
            _ => unimplemented!(),
        }
    }

    fn eval_tuple(&mut self, items: &[Expr]) -> Result<Value, ErrorBuf> {
        let mut data = vec![];
        for item in items.iter() {
            data.push(self.evaluate(item)?);
        }
        Ok(Value::Tuple(data))
    }

    fn eval_int_arr(&mut self, item: &Expr, reps: &Expr) -> Result<Value, ErrorBuf> {
        let reps = match self.evaluate(reps)? {
            Value::U32(n) => n as usize,
            _ => todo!(),
        };
        // NOTE: You cannot use `std::iter::repeat` to build this list, because
        // it might allocate!
        let mut data = vec![];
        for _ in 0..reps {
            data.push(self.evaluate(item)?)
        }
        Ok(Value::Array(data))
    }

    fn eval_ext_arr(&mut self, items: &[Expr]) -> Result<Value, ErrorBuf> {
        let mut ty = None;
        let mut data = vec![];
        for item in items.iter() {
            let val = self.evaluate(item)?;
            let next_ty = Some(val.type_of());
            data.push(val);

            if next_ty != ty {
                if ty == None {
                    ty = next_ty;
                } else {
                    // Error condition: not all the types are the same!
                    todo!();
                }
            }
        }
        Ok(Value::Array(data))
    }

    fn eval_unop(&mut self, op: &Token, right: &Expr) -> Result<Value, ErrorBuf> {
        use crate::circuit::Gate;
        use crate::token::Lexeme::*;
        let right_val = self.evaluate(right)?;
        let val = match (&op.lexeme, right_val) {
            (Tilde, Value::Bool(x)) => Value::Bool(!x),

            // NOTE: or-patterns syntax is experimental, so we must use this
            // more verbose syntax until it is stabilized.
            (Tilde, val @ Value::Q_Bool(_))
            | (Tilde, val @ Value::Q_U8(_))
            | (Tilde, val @ Value::Q_U16(_))
            | (Tilde, val @ Value::Q_U32(_)) => crate::functions::builtins::not(self, &[val])?,

            (Bang, val @ Value::Q_Bool(_))
            | (Bang, val @ Value::Q_U8(_))
            | (Bang, val @ Value::Q_U16(_))
            | (Bang, val @ Value::Q_U32(_)) => crate::functions::builtins::measure(self, &[val])?,

            (Question, Value::Bool(x)) => {
                let val = self.qubit_allocator.alloc_q_bool()?;
                if x {
                    if let Value::Q_Bool(u) = val {
                        self.compile_gate(Gate::X(u));
                    } else {
                        unreachable!();
                    }
                }
                val
            }

            (Question, Value::U8(x)) => {
                let val = self.qubit_allocator.alloc_q_u8()?;
                if let Value::Q_U8(qbs) = val {
                    for (i, qb) in qbs.iter().enumerate() {
                        if x & (1 << i) != 0 {
                            self.compile_gate(Gate::X(*qb))
                        }
                    }
                } else {
                    unreachable!();
                }
                val
            }

            (Question, Value::U16(x)) => {
                let val = self.qubit_allocator.alloc_q_u16()?;
                if let Value::Q_U16(qbs) = val {
                    for (i, qb) in qbs.iter().enumerate() {
                        if x & (1 << i) != 0 {
                            self.compile_gate(Gate::X(*qb))
                        }
                    }
                } else {
                    unreachable!();
                }
                val
            }

            (Question, Value::U32(x)) => {
                let val = self.qubit_allocator.alloc_q_u32()?;
                if let Value::Q_U32(qbs) = val {
                    for (i, qb) in qbs.iter().enumerate() {
                        if x & (1 << i) != 0 {
                            self.compile_gate(Gate::X(*qb))
                        }
                    }
                } else {
                    unreachable!();
                }
                val
            }

            (_, _) => panic!("Violated a typing invariant"),
        };
        Ok(val)
    }

    fn eval_binop(&mut self, left: &Expr, op: &Token, right: &Expr) -> Result<Value, ErrorBuf> {
        use crate::token::Lexeme;
        use crate::values::Value::*;
        let left = self.evaluate(left)?;
        let right = self.evaluate(right)?;
        let val = match op.lexeme {
            Lexeme::Plus => match (left, right) {
                (U8(x), U8(y)) => U8(x + y),
                (U16(x), U16(y)) => U16(x + y),
                (U32(x), U32(y)) => U32(x + y),
                (Array(ldata), Array(rdata)) => self.finish_array_sum(ldata, rdata)?,
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::Minus => match (left, right) {
                (U8(x), U8(y)) => U8(x.wrapping_sub(y)),
                (U16(x), U16(y)) => U16(x.wrapping_sub(y)),
                (U32(x), U32(y)) => U32(x.wrapping_sub(y)),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::Star => match (left, right) {
                (U8(x), U8(y)) => U8(x * y),
                (U16(x), U16(y)) => U16(x * y),
                (U32(x), U32(y)) => U32(x * y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::Percent => match (left, right) {
                (U8(x), U8(y)) => U8(x % y),
                (U16(x), U16(y)) => U16(x % y),
                (U32(x), U32(y)) => U32(x % y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::LAngle => match (left, right) {
                (U8(x), U8(y)) => Bool(x < y),
                (U16(x), U16(y)) => Bool(x < y),
                (U32(x), U32(y)) => Bool(x < y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::RAngle => match (left, right) {
                (U8(x), U8(y)) => Bool(x > y),
                (U16(x), U16(y)) => Bool(x > y),
                (U32(x), U32(y)) => Bool(x > y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::EqualEqual => match (left, right) {
                (Bool(x), Bool(y)) => Bool(x == y),
                (U8(x), U8(y)) => Bool(x == y),
                (U16(x), U16(y)) => Bool(x == y),
                (U32(x), U32(y)) => Bool(x == y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::TildeEqual => match (left, right) {
                (Bool(x), Bool(y)) => Bool(x != y),
                (U8(x), U8(y)) => Bool(x != y),
                (U16(x), U16(y)) => Bool(x != y),
                (U32(x), U32(y)) => Bool(x != y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::DotDot => match (left, right) {
                (U8(x), U8(y)) => Value::make_range(x, y),
                (U16(x), U16(y)) => Value::make_range(x, y),
                (U32(x), U32(y)) => Value::make_range(x, y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            _ => {
                panic!("illegal expression.");
            }
        };
        Ok(val)
    }

    fn finish_array_sum(
        &self,
        mut ldata: Vec<Value>,
        mut rdata: Vec<Value>,
    ) -> Result<Value, ErrorBuf> {
        use types::Type;
        // Time for some heavy dynamic typing
        let val = match (ldata.len(), rdata.len()) {
            (0, 0) => Value::Array(vec![]),
            (0, _) => Value::Array(rdata),
            (_, 0) => Value::Array(ldata),
            (_, _) => {
                if ldata[0].type_of() == rdata[0].type_of() {
                    ldata.append(&mut rdata);
                    Value::Array(ldata)
                } else {
                    // TODO this should be a type error
                    todo!();
                }
            }
        };
        Ok(val)
    }

    fn eval_call(&mut self, callee: &Ident, args: &[Expr]) -> Result<Value, ErrorBuf> {
        let args: Vec<Value> = args.iter().map(|arg| self.evaluate(arg).unwrap()).collect();

        let func = match self.env.get(&callee.name) {
            None => unreachable!(), // An earlier typing pass can eliminate this case
            Some(Moveable::There(Nameable::Value(_))) => todo!(), // Should return an error
            Some(Moveable::Moved) => todo!(), // Should return a different error
            // FIXME Ownership gets a little ugly here; let’s save ourselves a
            // little trouble for now, although this clone *could* be quite
            // expensive.
            Some(Moveable::There(Nameable::Func(func))) => func.clone(),
        };

        func.call(self, &args)
    }

    fn eval_index(&mut self, head: &Expr, index: &Expr) -> Result<Value, ErrorBuf> {
        use Value::{Array, Tuple, U32};
        let head = self.evaluate(head)?;
        let index = self.evaluate(index)?;
        match (head, index) {
            (Tuple(data), U32(n)) | (Array(data), U32(n)) => {
                let n = n as usize;
                if n < data.len() {
                    Ok(data[n].clone())
                } else {
                    // TODO PRIORITY 1
                    todo!("Error message here");
                }
            }
            (_, U32(_)) => panic!("Violated a typing invariant"),
            _ => unreachable!(),
        }
    }

    /// "Contravariant evaluation", the core logic of the control-flow blocks.
    /// This expresses any evaluation that takes place in a locally-transformed
    /// basis.
    ///
    /// TODO This design feels non-idiomatic. I should really think about how to
    /// simplify it, if possible.
    pub fn coevaluate<'b>(
        &'b mut self,
        expr: &Expr,
        func: &mut dyn FnMut(&mut Interpreter, Value) -> Result<Value, ErrorBuf>,
    ) -> Result<Value, ErrorBuf> {
        // We should have an invariant here that `self.contra_stack` is empty at
        // *this* point. We should verify that the error propatation operator
        // `?` below doesn't break this.
        self.set_contra(true);
        let basis = self.evaluate(expr)?;
        self.set_contra(false);
        // Run the callback
        let val = func(self, basis)?;
        // Pop the stack to uncompute.
        while let Some(gate) = self.contra_stack.pop() {
            self.emit_gate(gate);
        }
        // `self.contra_stack` is once again empty.
        Ok(val)
    }

    /// Sets flags for contravariant evaluation. An implementation detail of the
    /// `coevaluate` method.
    fn set_contra(&mut self, contra: bool) {
        self.contra = contra;
        self.env.moving = !contra;
    }

    pub fn interpret(&mut self, stmts: Vec<Stmt>) -> Result<(), ErrorBuf> {
        for stmt in stmts.into_iter() {
            self.execute(&stmt)?;
        }
        Ok(())
    }

    /////////////////////
    // Code generation //
    /////////////////////

    /// Generate code for a (non-elementary) gate.
    ///
    /// NOTE Like `eval_block`, this function is only public because it’s used
    /// by user-defined functions. It’s not clearly something that *should* be
    /// exposed as part of the compiler API.
    pub fn compile_gate(&mut self, gate: Gate) {
        let inner_gates = gate.controlled_on(self.env.controls());
        for inner_gate in inner_gates.into_iter() {
            self.emit_gate(inner_gate);
        }
    }

    /// This function should be called to insert a bare gate into the circuit.
    ///
    /// TODO Consider making this function take a wrapper type around Gate to
    /// ensure that it isn’t called in place to `compile_gate`.
    ///
    /// TODO I’d also like, instead of testing for a state flag, to do some kind
    /// of dynamic dispatch. Unfortunately this turns out to be pretty difficult
    /// in this context.
    fn emit_gate(&mut self, gate: Gate) {
        if self.contra {
            self.contra_stack.push(gate.clone().conjugate());
        }
        self.circuit.push_back(gate);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::Gate::*;
    use crate::parser::Parser;
    use crate::source::SrcObject;
    use crate::token::Lexeme;
    use crate::values::Value;

    //////////////////////////////////////////////////////
    // Functions and macros for constructing test cases //
    //////////////////////////////////////////////////////

    fn token(lexeme: Lexeme) -> Token {
        Token {
            lexeme,
            span: Span::default(),
        }
    }

    /// We'll use this macro to test the interpreter. This evaluates a single
    /// expression and tests its value
    macro_rules! test_interpreter {
        ($code:expr ; $tok:ident$(($($arg:expr),+))?) => {
            let expected_value = Value::$tok $(($($arg),+))?;

            let src = SrcObject::from($code);
            let tokens = Scanner::new(&src).tokenize().unwrap();
            let ast = Parser::new(tokens).expression().unwrap();
            let arch = Arch::default();
            let actual_value = Interpreter::new(&arch).evaluate(&ast);

            assert_eq!(expected_value, actual_value.unwrap());
        };
    }

    fn test_program(prog: &'static str, expected_gates: Vec<Gate>) {
        let src = SrcObject::from(prog);

        let tokens = Scanner::new(&src).tokenize().unwrap();
        let stmts = Parser::new(tokens).parse().unwrap();
        let arch = Arch::default();
        let mut interp = Interpreter::new(&arch);
        for stmt in stmts.into_iter() {
            interp.execute(&stmt).unwrap();
        }

        // TODO not necessarily the same length
        let empirical_gates = interp.circuit.circ_buf;
        assert_eq!(expected_gates.len(), empirical_gates.len());
        let pairs = empirical_gates.iter().zip(expected_gates);
        for (expected, actual) in pairs {
            assert_eq!(expected, &actual)
        }
    }

    ///////////////////
    // Simple values //
    ///////////////////

    #[test]
    fn addition_simple() {
        test_interpreter! {
            "1 + 1"; U32(2)
        };
    }

    #[test]
    fn multiplication_simple() {
        test_interpreter! {
            "2 * 3"; U32(6)
        };
    }

    #[test]
    fn addition_multiple() {
        test_interpreter! {
            "1 + 2 + 3"; U32(6)
        };
    }

    #[test]
    fn multiplication_multiple() {
        test_interpreter! {
            "2 * 3 * 4"; U32(24)
        };
    }

    #[test]
    fn parens_left() {
        test_interpreter! {
            "(2 * 3) + 4"; U32(10)
        }
    }

    #[test]
    fn parens_right() {
        test_interpreter! {
            "2 * (3 + 4)"; U32(14)
        }
    }

    #[test]
    fn bool_simple() {
        test_interpreter! {
            "true"; Bool(true)
        }
    }

    #[test]
    fn bool_binop() {
        test_interpreter! {
            "true != false"; Bool(true)
        }
    }

    #[test]
    fn cmp_lt_simple() {
        test_interpreter! {
            "3 < 4"; Bool(true)
        }
    }

    #[test]
    fn cmp_gt_simple() {
        test_interpreter! {
            "3 > 4"; Bool(false)
        }
    }

    #[test]
    fn mixed_arith_eq() {
        test_interpreter! {
            "2 + 2 == 4"; Bool(true)
        }
    }

    #[test]
    fn mixed_complex() {
        test_interpreter! {
            "(2 + 2 < 2 * 1) == (false ~= true)"; Bool(false)
        }
    }

    #[test]
    fn range_simple() {
        use Value::*;
        test_interpreter! {
            "0..5";
            Array(vec![U32(0), U32(1), U32(2), U32(3), U32(4)])
        }
    }

    #[test]
    fn array_concat() {
        use Value::*;
        test_interpreter! {
            "[false, false] + [true, false]";
            Array(vec![Bool(false), Bool(false), Bool(true), Bool(false)])
        }
    }

    //////////////
    // Programs //
    //////////////

    #[test]
    fn simple_program() {
        test_program("let x = ?true;", vec![X(0)]);
    }

    #[test]
    fn single_cnot() {
        let prog = r#"
        let x = ?false;
        let y = ?false;
        if y {
            let x = ~x;
        }
        "#;
        test_program(prog, vec![CX { ctrl: 1, tgt: 0 }]);
    }

    #[test]
    fn controlled_z() {
        let prog = r#"
        let x = ?false;
        let y = ?false;
        if y {
            let x = flip(x);
        }
        "#;
        test_program(prog, vec![H(0), CX { ctrl: 1, tgt: 0 }, H(0)]);
    }

    #[test]
    fn simple_uncomputation() {
        let prog = r#"
        let x = ?false;
        let y = split(x) in {
            let y = ~y;
        }
        let x = flip(x);
        "#;
        test_program(prog, vec![H(0), X(0), H(0), Z(0)])
    }

    #[test]
    fn simple_loop() {
        let prog = r#"
        let arr = [?false; 3];
        for q in arr {
            let q = ~q;
        }
        "#;
        test_program(prog, vec![X(0), X(1), X(2)])
    }

    #[test]
    fn simple_function() {
        let prog = r#"
        let x = ?false;
        fn inv(y: ?bool) {
            let y = ~y;
        } 
        inv(x);
        "#;
        test_program(prog, vec![X(0)]);
    }

    #[test]
    fn simple_function_with_capture() {
        let prog = r#"
        let x = ?false;
        fn inv() {
            let x = ~x;
        } 
        inv();
        "#;
        test_program(prog, vec![X(0)]);
    }

    #[test]
    fn simple_function_multiple_statements() {
        let prog = r#"
        let x = ?false;
        fn inv(y: ?bool) {
            let y = ~y;
            let y = ~y;
        } 
        inv(x);
        "#;
        test_program(prog, vec![X(0), X(0)]);
    }

    #[test]
    fn simple_function_with_return() {
        let prog = r#"
        let x = ?false;
        fn inv(y: ?bool) {
            ~y
        } 
        let x = inv(x);
        "#;
        test_program(prog, vec![X(0)]);
    }

    #[test]
    fn quantum_integer() {
        let prog = r#"
        let x = ?147;
        "#;
        test_program(prog, vec![X(0), X(1), X(4), X(7)])
    }

    #[test]
    fn simple_measurement() {
        let prog = r#"
        let x = ?true;
        !x;
        "#;
        test_program(prog, vec![X(0), M(0)])
    }

    #[test]
    fn bitwise_boradcast() {
        let prog = r#"
        let x = split(?0);
        !x;
        "#;
        let mut gates = vec![];
        for i in 0..32 {
            gates.push(H(i));
        }
        for i in 0..32 {
            gates.push(M(i));
        }
        test_program(prog, gates)
    }

    #[test]
    fn meas_results_copyable() {
        let prog = r#"
        let n = split(?false);
        let m = !n;
        let m2 = m;
        let m3 = m;
        "#;
        test_program(prog, vec![H(0), M(0)])
    }

    #[test]
    fn array_linear_concat() {
        let prog = r#"
        let a = [?true, ?true];
        let b = [?true, ?true];
        let c = a + b;
        "#;
        test_program(prog, vec![X(0), X(1), X(2), X(3)])
    }

    #[test]
    #[should_panic]
    fn array_linearity_violation() {
        let prog = r#"
        let a = [?true, ?true];
        let b = [?true, ?true];
        let c = a + b;
        let d = a + b;
        "#;
        test_program(prog, vec![X(0), X(1), X(2), X(3)])
    }

    #[test]
    fn array_index_simple() {
        let prog = r#"
        let arr = [?false; 3];
        let q = ~arr[2];
        "#;
        test_program(prog, vec![X(2)])
    }

    #[test]
    fn array_index_nested() {
        let prog = r#"
        let arr = [[?false; 2]; 3];
        let q = ~arr[2][1];
        "#;
        test_program(prog, vec![X(5)])
    }

    #[test]
    fn array_destructuring_simple() {
        let prog = r#"
        let arr = [?false; 3];
        let (q, r, s) = arr;
        let r = ~r;
        "#;
        test_program(prog, vec![X(1)])
    }

    #[test]
    #[should_panic]
    fn destructuring_linearity_violation() {
        let prog = r#"
        let arr = [?false; 3];
        let (q, r, s) = arr;
        let r = ~r;
        let t = arr[0];
        "#;
        test_program(prog, vec![X(1)])
    }

    #[test]
    fn tuple_destructuring_nested() {
        let prog = r#"
        let data = ((?false, ?false), (?true, ?true));
        let ((a, b), (c, d)) = data;
        let b = split(b);
        "#;
        test_program(prog, vec![X(2), X(3), H(1)])
    }

    #[test]
    fn tuple_index_simple() {
        let prog = r#"
        let arr = (?false, ?false, ?false);
        let q = ~arr[2];
        "#;
        test_program(prog, vec![X(2)])
    }

    #[test]
    fn mixed_loop_conditional_1() {
        let prog = r#"
        let arr = [?false; 5];
        for i in 0..len(arr) {
            if i > 2 {
                let q = arr[i] in {
                    let q = ~q;
                }
            }
        }
        "#;
        test_program(prog, vec![X(3), X(4)])
    }

    #[test]
    fn mixed_loop_conditional_2() {
        let prog = r#"
        let arr = [?false; 5];
        for (i, q) in enumerate(arr) {
            if i > 2 {
                let q = ~q;
            }
        }
        "#;
        test_program(prog, vec![X(3), X(4)])
    }

    #[test]
    fn multiple_return_ebit() {
        let prog = r#"
        fn ebit() {
            let p = split(?false);
            let q = ?false;
            if p {
                let q = ~q;
            }
            (p, q)
        }

        let (p, q) = ebit();
        "#;
        test_program(prog, vec![H(0), CX { ctrl: 0, tgt: 1 }]);
    }
}
