use crate::alloc::QubitAllocator;
use crate::arch::Arch;
use crate::ast::{Expr, Stmt};
use crate::environment::{Environment, Key, Moveable, Nameable};
use crate::errors::ErrorBuf;
use crate::parser::ParseError;
use crate::qram::Qram;
use crate::scanner::{ScanError, Scanner};
use crate::token::{Lexeme, Token};
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
    token: Option<Token>,
}

impl fmt::Display for InterpreterError {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.token {
            Some(token) => {
                write!(f, "Interpreter error at `{}` [{}]: {}",
                       token, token.loc, self.msg)
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
        use Stmt::*;
        match stmt {
            Print(expr) => {
                println!("{}", self.evaluate(expr)?);
                Ok(())
            },
            Assn { lhs, rhs } => self.exec_assn(lhs, rhs),
            For { bind, iter, body } => self.exec_for(bind, iter, body),
            Fn { name, params, body } => self.exec_fn(name, params, body),
            Expr(expr) => {
                self.evaluate(expr)?;
                Ok(())
            }
        }
    }

    #[rustfmt::skip]
    fn exec_assn(&mut self, lhs: &Expr, rhs: &Expr) -> Result<(), ErrorBuf> {
        use {Lexeme::Ident, Expr::Variable};
        if let Variable(Token { lexeme: Ident(name), loc: _ }) = lhs {
            let rhs_val = self.evaluate(rhs)?;
            self.env.insert(name.clone(), Nameable::Value(rhs_val));
        } else {
            panic!("Only support identifier lhs.");
        }
        Ok(())
    }

    /// Calling this function is how Cavy functions are defined. This has some
    /// weird consequences. One is that in nested functions, or functions
    /// defined in loops, they are redefined every time they are encountered. I
    /// think function definitions should maybe be resolved at some *earlier*
    /// time, before evaluation.
    fn exec_fn(&mut self, name: &Token, params: &[Token], body: &Expr) -> Result<(), ErrorBuf> {
        let name = match &name.lexeme {
            Lexeme::Ident(name) => name.clone(),
            _ => unreachable!(),
        };
        let params = params
            .iter()
            .map(|param| match &param.lexeme {
                Lexeme::Ident(param_name) => param_name.clone(),
                _ => unreachable!(),
            })
            .collect::<Vec<String>>();
        let body = Box::new(body.clone());

        self.env
            .insert(name, Nameable::Func(Rc::new(UserFunc { params, body })));

        Ok(())
    }

    fn eval_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Option<Box<Expr>>,
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
        then_branch: &Expr,
        else_branch: &Option<Box<Expr>>,
    ) -> Result<Value, ErrorBuf> {
        use Expr::Block;
        match cond_val {
            // FIXME This is less than half of an implementation!
            Value::Q_Bool(u) => {
                // FIXME This is far from a proper and complete solution to the
                // evaluation of If expressions. For one thing, they’re
                // dynamically typed: the return values are not guaranteed to be
                // the same type, and it might only fail contingently at
                // runtime. Also, there isn’t as strong of a distinction between
                // If statements and If expressions as feels appropriate.
                match (then_branch, else_branch) {
                    (Block(then_body, then_expr), None) => {
                        let controls = vec![*u];
                        self.eval_block(then_body, then_expr, None, controls)?;
                        Ok(Value::Unit)
                    }
                    _ => {
                        todo!();
                    }
                }
            }
            Value::Bool(_) => {
                if cond_val.is_truthy() {
                    self.evaluate(then_branch)
                } else if let Some(else_branch) = else_branch {
                    self.evaluate(else_branch)
                } else {
                    Ok(Value::Unit)
                }
            }
            _ => panic!("Violated a typing invariant"),
        }
    }

    fn exec_for(&mut self, bind: &Expr, iter: &Expr, body: &Expr) -> Result<(), ErrorBuf> {
        self.coevaluate(iter, &mut |self_, iter_val| {
            self_.eval_for_inner(bind, &iter_val, body)
        })?;
        Ok(())
    }

    // Yes, this one is called `eval` because the blocks are actually
    // expressions; we're just dumping the return values.
    fn eval_for_inner(
        &mut self,
        bind: &Expr,
        iter: &Value,
        body: &Expr,
    ) -> Result<Value, ErrorBuf> {
        use Expr::{Block, Variable};
        use Lexeme::Ident;

        // Unwrap the data for now.
        let iter = match iter {
            Value::Array(data) => data,
            _ => panic!(),
        };

        match (bind, body) {
            // NOTE it's not ideal that this accepcs a Block that may return
            // something, then simply *ignores* the return value.
            (
                Variable(Token {
                    lexeme: Ident(name),
                    ..
                }),
                Block(stmts, None),
            ) => {
                for item in iter.iter() {
                    let mut bindings = HashMap::new();
                    // This clone shouldn't *really* be necessary; the block
                    // itself confers a natural lifetime on the value.
                    bindings.insert(name.to_owned(), Nameable::Value(item.clone()));
                    self.eval_block(stmts, &None, Some(bindings), vec![])?;
                }
            }
            (_, Block(_, _)) => {
                panic!("Only support identifier 'for' loop bindings.");
            }
            (_, _) => unreachable!(),
        };
        Ok(Value::Unit)
    }

    fn eval_let(&mut self, lhs: &Expr, rhs: &Expr, body: &Expr) -> Result<Value, ErrorBuf> {
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

    fn eval_let_inner(&mut self, lhs: &Expr, rhs: &Value, body: &Expr) -> Result<Value, ErrorBuf> {
        use {
            Expr::{Block, Variable},
            Lexeme::Ident,
        };
        match (lhs, body) {
            (
                Variable(Token {
                    lexeme: Ident(name),
                    ..
                }),
                Block(stmts, expr),
            ) => {
                let mut bindings = HashMap::new();
                // FIXME these `to_owned` and `clone` *shouldn't* be necessary.
                bindings.insert(name.to_owned(), Nameable::Value(rhs.clone()));
                self.eval_block(stmts, expr, Some(bindings), vec![])
            }

            (_, Block(_, _)) => {
                panic!("Only support identifier lhs.");
            }

            (_, _) => unreachable!(),
        }
    }

    ///////////////////////////
    // Expression evaluation //
    ///////////////////////////

    /// Evaluate an expression
    pub fn evaluate(&mut self, expr: &Expr) -> Result<Value, ErrorBuf> {
        use Expr::*;
        match expr {
            BinOp { left, op, right } => self.eval_binop(left, op, right),
            UnOp { op, right } => self.eval_unop(op, right),
            Literal(literal) => self.eval_literal(literal),
            Variable(variable) => self.eval_variable(variable),
            IntArr { item, reps } => self.eval_int_arr(item, reps),
            ExtArr(items) => self.eval_ext_arr(items),
            Group(expr) => self.evaluate(expr),
            If {
                cond,
                then_branch,
                else_branch,
            } => self.eval_if(cond, then_branch, else_branch),
            Let { lhs, rhs, body } => self.eval_let(lhs, rhs, body),
            Block(stmts, expr) => self.eval_block(stmts, expr, None, vec![]),
            Call { callee, args, .. } => self.eval_call(callee, args),
            Index { head, index, .. } => self.eval_index(head, index),
        }
    }

    /// NOTE This function is only public because it’s used by user-defined
    /// functions. It’s not clearly something that *should* be exposed as part
    /// of the compiler API.
    pub fn eval_block(
        &mut self,
        stmts: &[Stmt],
        expr: &Option<Box<Expr>>,
        bindings: Option<HashMap<Key, Nameable>>,
        controls: Vec<Qubit>,
    ) -> Result<Value, ErrorBuf> {
        self.env.open_scope(bindings, controls);
        let val = self.eval_block_inner(stmts, expr);
        self.env.close_scope();
        val
    }

    fn eval_block_inner(
        &mut self,
        stmts: &[Stmt],
        expr: &Option<Box<Expr>>,
    ) -> Result<Value, ErrorBuf> {
        for stmt in stmts.iter() {
            self.execute(stmt)?;
        }
        match expr {
            Some(expr) => self.evaluate(expr),
            None => Ok(Value::Unit),
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

    fn eval_variable(&mut self, variable: &Token) -> Result<Value, ErrorBuf> {
        use crate::token::Lexeme;
        use Moveable::*;
        match &variable.lexeme {
            Lexeme::Ident(name) => {
                // About this unwrap: we will at some point in the (hopefully
                // near) future track whether this operation is safe statically,
                // and always know when there is a value in the environment.
                match self.env.get(&name) {
                    Some(There(Nameable::Value(val))) => Ok(val),
                    Some(Moved) => {
                        let err = InterpreterError {
                            msg: format!("the variable `{}` has been moved.", name),
                            token: Some(variable.clone()),
                        };
                        Err(ErrorBuf(vec![Box::new(err)]))
                    }
                    None => {
                        let err = InterpreterError {
                            msg: format!("the name `{}` is unbound.", name),
                            token: Some(variable.clone()),
                        };
                        Err(ErrorBuf(vec![Box::new(err)]))
                    }
                    // In the near-term this should just be an error; in the
                    // long term, there should be first-class functions.
                    _ => unimplemented!(),
                }
            }
            _ => panic!("Invariant violation!"),
        }
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
        let left_val = self.evaluate(left)?;
        let right_val = self.evaluate(right)?;
        let val = match op.lexeme {
            Lexeme::Plus => match (left_val, right_val) {
                (U8(x), U8(y)) => U8(x + y),
                (U16(x), U16(y)) => U16(x + y),
                (U32(x), U32(y)) => U32(x + y),
                (Array(ldata), Array(rdata)) => self.finish_array_sum(ldata, rdata)?,
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::Star => match (left_val, right_val) {
                (U8(x), U8(y)) => U8(x * y),
                (U16(x), U16(y)) => U16(x * y),
                (U32(x), U32(y)) => U32(x * y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::LAngle => match (left_val, right_val) {
                (U8(x), U8(y)) => Bool(x < y),
                (U16(x), U16(y)) => Bool(x < y),
                (U32(x), U32(y)) => Bool(x < y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::RAngle => match (left_val, right_val) {
                (U8(x), U8(y)) => Bool(x > y),
                (U16(x), U16(y)) => Bool(x > y),
                (U32(x), U32(y)) => Bool(x > y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::EqualEqual => match (left_val, right_val) {
                (Bool(x), Bool(y)) => Bool(x == y),
                (U8(x), U8(y)) => Bool(x == y),
                (U16(x), U16(y)) => Bool(x == y),
                (U32(x), U32(y)) => Bool(x == y),
                (_, _) => panic!("Violated a typing invariant"),
            },
            Lexeme::TildeEqual => match (left_val, right_val) {
                (Bool(x), Bool(y)) => Bool(x != y),
                (U8(x), U8(y)) => Bool(x != y),
                (U16(x), U16(y)) => Bool(x != y),
                (U32(x), U32(y)) => Bool(x != y),
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
        use values::types::Type;
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

    fn eval_call(&mut self, callee: &Token, args: &[Expr]) -> Result<Value, ErrorBuf> {
        let callee = match callee {
            Token {
                lexeme: Lexeme::Ident(id),
                loc: _,
            } => id,
            _ => panic!("Violated a typing invariant"),
        };

        let args: Vec<Value> = args.iter().map(|arg| self.evaluate(arg).unwrap()).collect();

        let func = match self.env.get(callee) {
            None => unreachable!(), // An earlier typing pass can eliminate this case
            Some(Moveable::There(Nameable::Value(_))) => todo!(), // Should return an error
            Some(Moveable::Moved) => todo!(), // Should return a different error
            // FIXME Ownership gets a little ugly here; let’s save ourself a
            // little trouble for now, although this clone *could* be quite
            // expensive.
            Some(Moveable::There(Nameable::Func(func))) => func.clone(),
        };

        func.call(self, &args)
    }

    fn eval_index(&mut self, head: &Expr, index: &Expr) -> Result<Value, ErrorBuf> {
        use Value::{Array, U32};
        let head = self.evaluate(head)?;
        let index = self.evaluate(index)?;
        match (head, index) {
            (Array(data), U32(n)) => {
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
    use crate::scanner::SourceCode;
    use crate::token::{Lexeme, Location};
    use crate::values::Value;

    //////////////////////////////////////////////////////
    // Functions and macros for constructing test cases //
    //////////////////////////////////////////////////////

    fn token(lexeme: Lexeme) -> Token {
        Token {
            lexeme,
            loc: Location::default(),
        }
    }

    /// We'll use this macro to test the interpreter. This evaluates a single
    /// expression and tests its value
    macro_rules! test_interpreter {
        ($code:expr ; $tok:ident$(($($arg:expr),+))?) => {
            let expected_value = Value::$tok $(($($arg),+))?;

            let src = SourceCode {
                code: $code.chars().peekable(),
                file: None,
            };

            let tokens = Scanner::new(src).tokenize().unwrap();
            let ast = Parser::new(tokens).expression().unwrap();
            let arch = Arch::default();
            let actual_value = Interpreter::new(&arch).evaluate(&ast);

            assert_eq!(expected_value, actual_value.unwrap());
        };
    }

    fn test_program(prog: &'static str, expected_gates: Vec<Gate>) {
        let src = SourceCode {
            code: prog.chars().peekable(),
            file: None,
        };

        let tokens = Scanner::new(src).tokenize().unwrap();
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
        fn inv(y) {
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
        fn inv(y) {
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
        fn inv(y) {
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
}
