use crate::ast::{Expr, Stmt};
use crate::environment::{Environment, Key, Nameable};
use crate::errors::ErrorBuf;
use crate::parser::ParseError;
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

pub trait Allocator<T> {
    fn alloc_one(&mut self) -> T;
    fn free_one(&mut self, value: T);
}

#[derive(Default)]
pub struct QubitAllocator {
    least_free: usize,
    freed: HashSet<usize>,
}

impl QubitAllocator {
    fn new() -> Self {
        Self::default()
    }
}

impl Allocator<Value> for QubitAllocator {
    fn alloc_one(&mut self) -> Value {
        let new_index = self.least_free;
        self.least_free += 1;
        Value::Q_Bool(new_index)
    }

    fn free_one(&mut self, value: Value) {
        match value {
            Value::Q_Bool(index) => {
                // Insert it into the list of freed values, and panic if you’ve
                // freed the element before.
                if !self.freed.insert(index) {
                    panic!();
                }
            }
            _ => {
                // This shouldn’t be possible.
                panic!();
            }
        }
    }
}

pub struct Interpreter {
    pub env: Environment,
    pub circuit: Circuit,
    pub qubit_allocator: Box<dyn Allocator<Value>>,
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

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Environment::base(),
            circuit: Circuit::new(),
            qubit_allocator: Box::new(QubitAllocator::new()),
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
                println!("{:?}", self.evaluate(expr)?);
            },
            Assn { lhs, rhs } => {
                self.exec_assn(lhs, rhs)?;
            },
            // Function definition
            Fn { name, params, body } => self.exec_fn(name, params, body)?,
            stmt => {
                println!("{:?}", stmt);
                todo!();
            }
        }
        Ok(())
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
        else_branch: &Expr,
    ) -> Result<Value, ErrorBuf> {
        // Note that `self` is passed as a parameter to the closure, rather than
        // captured from the environment. The latter would violate the borrow
        // checker rules by making a second mutable borrow.
        //
        // NOTE This may not be very idiomatic, and it’s not unlikely that a
        // future refactoring will replace this pattern entirely.
        self.coevaluate(cond, &mut |self_, cond_val| {
            self_.eval_if_inner(&cond_val, then_branch, else_branch)
        })
    }

    #[rustfmt::skip]
    fn eval_if_inner(
        &mut self,
        cond_val: &Value,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> Result<Value, ErrorBuf> {
        match cond_val {
            // FIXME This is less than half of an implementation!
            Value::Q_Bool(u) => {
                // Let’s not handle If *expressions* in the linear case just
                // yet. I’m not really sure what the correct semantics are for
                // something like:
                //
                // ```
                // p = if q {
                //   r
                // } else {
                //   s
                // };
                // ```
                //
                // where q, r, and s are all qubits. You could return an ancilla
                // controlled r and s (controlled and anticontrolled,
                // respectively, on q), but this seems to violate linearity.
                // Maybe introducing a concept of borrowing would be a way to
                // resolve this.
                //
                // FIXME In any case, this exclusion is terribly ad-hoc and
                // should be enforced in some other way, if it *must* remain.
                match (then_branch, else_branch) {
                    (Expr::Block(_, Some(_)), _) => {
                        unimplemented!();
                    },
                    (_, Expr::Block(_, Some(_))) => {
                        unimplemented!();
                    },
                    (Expr::Block(then_body, None), Expr::Block(_, None)) => {
                        // Now the implementation for the non-excluded cases. (We should
                        // actually spawn a new environment in the block, in which the
                        // extra control has been added. This is merely piling ad-hoc
                        // solution on ad-hoc solution.)
                        let mut controls = HashSet::new();
                        controls.insert(*u);
                        self.eval_block(then_body, &None, None, Some(controls))
                        // ...And ignore the else branch for now.
                    }
                     _ => {
                         unimplemented!();
                     }
                }

            },
            Value::Bool(_) => {
                if cond_val.is_truthy() {
                    self.evaluate(then_branch)
                } else {
                    self.evaluate(else_branch)
                }
            },
            _ => panic!("Violated a typing invariant"),
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
            Group(expr) => self.evaluate(expr),
            If {
                cond,
                then_branch,
                else_branch,
            } => self.eval_if(cond, then_branch, else_branch),
            Block(stmts, expr) => self.eval_block(stmts, expr, None, None),
            Call {
                callee,
                args,
                paren: _,
            } => self.eval_call(callee, args),
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
        controls: Option<HashSet<Qubit>>,
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
        match &variable.lexeme {
            Lexeme::Ident(name) => {
                // About this unwrap: we will at some point in the (hopefully
                // near) future track whether this operation is safe statically,
                // and always know when there is a value in the environment.
                let val = self.env.get(&name).unwrap();
                match val {
                    Nameable::Value(val) => Ok(val),
                    // In the near-term this should just be an error; in the
                    // long term, there should be first-class functions.
                    _ => unimplemented!(),
                }
            }
            _ => panic!("Invariant violation!"),
        }
    }

    fn eval_unop(&mut self, op: &Token, right: &Expr) -> Result<Value, ErrorBuf> {
        use crate::circuit::Gate;
        use crate::token::Lexeme::*;
        let right_val = self.evaluate(right)?;
        let val = match (&op.lexeme, right_val) {
            (Tilde, Value::Bool(x)) => Value::Bool(!x),
            (Tilde, Value::Q_Bool(u)) => {
                self.compile_gate(Gate::X(u));
                Value::Q_Bool(u)
            }

            (Question, Value::Bool(x)) => {
                let val = self.qubit_allocator.alloc_one();
                if x {
                    if let Value::Q_Bool(u) = val {
                        self.compile_gate(Gate::X(u));
                    } else {
                        unreachable!();
                    }
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
            Some(Nameable::Value(_)) => todo!(), // Should return an error

            // FIXME Ownership gets a little ugly here; let’s save ourself a
            // little trouble for now, although this clone *could* be quite
            // expensive.
            Some(Nameable::Func(func)) => func.clone(),
        };

        func.call(self, &args)

        // if args.len() != func.params.len() {
        //     todo!(); // Should also return an error
        // }

        // // TODO this is really *not correct*: arguments should be
        // // coevaluated. Because I don’t want to deal with that just yet, I’m
        // // accepting only identifier arguments.
        // //
        // // Actually, on second though, should they be? Maybe there should
        // // really be a distinction between passing by value and passing by
        // // reference.
        // //
        // // FIXME unwrap for testing
        // let bindings: HashMap<Key, Nameable> = func
        //     .params
        //     .iter()
        //     .zip(args.into_iter())
        //     .map(|(key, val)| (key.clone(), Nameable::Value(val)))
        //     .collect();

        // match &*func.body {
        //     Expr::Block(body, expr) => self.eval_block(&body, &expr, Some(bindings), None),
        //     _ => unreachable!(),
        // }
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

    pub fn interpret(&mut self, _input: &str) -> Result<(), ErrorBuf> {
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
            let actual_value = Interpreter::new().evaluate(&ast);

            assert_eq!(expected_value, actual_value.unwrap());
        };
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
}
