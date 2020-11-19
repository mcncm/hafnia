use crate::ast::{Expr, Stmt};
use crate::environment::Environment;
use crate::parser::ParseError;
use crate::scanner::{ScanError, Scanner};
use crate::token::{Lexeme, Token};
use crate::{
    circuit::{Circuit, Gate, Qubit},
    values::Value,
};
use std::error::Error;
use std::{collections::HashSet, fmt};

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

pub struct Interpreter<'a> {
    pub env: Environment<'a>,
    pub circuit: Circuit,
    pub qubit_allocator: Box<dyn Allocator<Value>>,
}

impl<'a> Interpreter<'a> {
    pub fn new() -> Self {
        Interpreter {
            env: Environment::new(),
            circuit: Circuit::new(),
            qubit_allocator: Box::new(QubitAllocator::new()),
        }
    }

    /////////////////////////
    // Statement execution //
    /////////////////////////

    #[rustfmt::skip]
    pub fn execute(&mut self, stmt: &Stmt) -> Result<(), Vec<Box<dyn Error>>> {
        use crate::ast::Expr;
        use Stmt::*;
        match stmt {
            Print(expr) => {
                println!("{:?}", self.evaluate(expr)?);
            },
            Assn { lhs, rhs } => {
                self.exec_assn(lhs, rhs)?;
            },
            If { cond, then_branch, else_branch } => {
                self.exec_if(cond, then_branch, else_branch)?;
            },
            Block(stmts) => {
                for stmt in stmts.iter() {
                    self.execute(stmt)?;
                }
            },
            stmt => {
                println!("{:?}", stmt);
                todo!();
            }
        }
        Ok(())
    }

    #[rustfmt::skip]
    fn exec_assn(&mut self, lhs: &Expr, rhs: &Expr) -> Result<(), Vec<Box<dyn Error>>> {
        use {Lexeme::Ident, Expr::Variable};
        if let Variable(Token { lexeme: Ident(name), loc: _ }) = lhs {
            let rhs_val = self.evaluate(rhs)?;
            self.env.insert(name.clone(), rhs_val);
        } else {
            panic!("Only support identifier lhs.");
        }
        Ok(())
    }

    #[rustfmt::skip]
    fn exec_if(
        &mut self,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Box<Stmt>>,
    ) -> Result<(), Vec<Box<dyn Error>>> {
        // TODO this is not yet proper coevaluation. Instead, `exec_if` should
        // probably take cond_val as already computed, and this function should
        // be passed into `coevaluate` as a parameter.
        let cond_val = self.coevaluate(cond)?;
        match cond_val {
            Value::Q_Bool(u) => {
                // TODO This demands abstraction! It’s really messy, and
                // horrible obscures the structure of the problem. 
                self.env.controls.insert(u);
                self.execute(then_branch)?;
                self.env.controls.remove(&u);
                if let Some(else_branch) = else_branch {
                    self.emit_gate(Gate::X(u));
                    self.env.controls.insert(u);
                    self.execute(else_branch)?;
                    self.env.controls.remove(&u);
                    self.emit_gate(Gate::X(u));
                }
            }
            Value::Bool(_) => {
                if cond_val.is_truthy() {
                    self.execute(then_branch)?;
                } else if let Some(stmt) = else_branch {
                    self.execute(stmt)?;
                }
            }
            _ => panic!("Violated a typing invariant"),
        }
        Ok(())
    }

    ///////////////////////////
    // Expression evaluation //
    ///////////////////////////

    /// Evaluate an expression
    pub fn evaluate(&mut self, expr: &Expr) -> Result<Value, Vec<Box<dyn Error>>> {
        use Expr::*;
        match expr {
            BinOp { left, op, right } => self.eval_binop(left, op, right),
            UnOp { op, right } => self.eval_unop(op, right),
            Literal(literal) => self.eval_literal(literal),
            Variable(variable) => self.eval_variable(variable),
            Group(expr) => self.evaluate(expr),
        }
    }

    fn eval_literal(&self, literal: &Token) -> Result<Value, Vec<Box<dyn Error>>> {
        use crate::token::Lexeme;
        // TODO
        match literal.lexeme {
            Lexeme::Nat(nat) => Ok(Value::U32(nat)),
            Lexeme::True => Ok(Value::Bool(true)),
            Lexeme::False => Ok(Value::Bool(false)),
            _ => todo!(),
        }
    }

    fn eval_variable(&mut self, variable: &Token) -> Result<Value, Vec<Box<dyn Error>>> {
        use crate::token::Lexeme;
        match &variable.lexeme {
            Lexeme::Ident(name) => {
                // About this unwrap: we will at some point in the (hopefully
                // near) future track whether this operation is safe statically,
                // and always know when there is a value in the environment.
                let val = self.env.get(&name).unwrap();
                Ok(*val)
            }
            _ => panic!("Invariant violation!"),
        }
    }

    fn eval_unop(&mut self, op: &Token, right: &Expr) -> Result<Value, Vec<Box<dyn Error>>> {
        use crate::circuit::Gate;
        use crate::token::Lexeme::*;
        let right_val = self.evaluate(right)?;
        let val = match (&op.lexeme, right_val) {
            (Tilde, Value::Bool(x)) => Value::Bool(!x),
            (Tilde, Value::Q_Bool(u)) => {
                self.emit_gate(Gate::X(u));
                Value::Q_Bool(u)
            }

            (Question, Value::Bool(x)) => {
                let val = self.qubit_allocator.alloc_one();
                if x {
                    if let Value::Q_Bool(u) = val {
                        self.emit_gate(Gate::X(u));
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

    fn eval_binop(
        &mut self,
        left: &Expr,
        op: &Token,
        right: &Expr,
    ) -> Result<Value, Vec<Box<dyn Error>>> {
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

    pub fn coevaluate(&mut self, expr: &Expr) -> Result<Value, Vec<Box<dyn Error>>> {
        // TODO
        self.evaluate(expr)
    }

    pub fn interpret(&mut self, _input: &str) -> Result<(), Vec<Box<dyn Error>>> {
        Ok(())
    }

    // pub fn with_control(&mut self, ctrl: Qubit, f: Box<dyn FnMut() -> ()>) {
    //     self.env.controls.insert(ctrl);
    //     f();
    //     self.env.controls.remove(&ctrl);
    // }

    /////////////////////
    // Code generation //
    /////////////////////

    pub fn emit_gate(&mut self, gate: Gate) {
        self.circuit.push_back(gate, &self.env.controls);
    }
}

pub struct CodeObject {
    // TODO
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::scanner::SourceObject;
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

            let src = SourceObject {
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
