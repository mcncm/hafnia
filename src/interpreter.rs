use crate::ast::Expr;
use crate::environment::Environment;
use crate::parser::ParseError;
use crate::scanner::{ScanError, Scanner};
use crate::token::Token;
use crate::values::Value;
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

pub struct Interpreter {
    pub env: Environment,
    pub qubit_allocator: Box<dyn Allocator<Value>>,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Environment::new(),
            qubit_allocator: Box::new(QubitAllocator::new()),
        }
    }

    /// Evaluate an expression
    pub fn evaluate(&mut self, expr: &Expr) -> Result<Value, Vec<Box<dyn Error>>> {
        use crate::ast::Expr::*;
        match expr {
            BinOp { left, op, right } => self.eval_binop(left, op, right),
            UnOp { op, right } => self.eval_unop(op, right),
            Literal(literal) => self.eval_literal(literal),
            Variable(_) => {
                todo!();
            }
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

    fn eval_unop(&mut self, op: &Token, right: &Expr) -> Result<Value, Vec<Box<dyn Error>>> {
        use crate::token::Lexeme::*;
        let right_val = self.evaluate(right)?;
        let val = match (&op.lexeme, right_val) {
            (Tilde, Value::Bool(x)) => Value::Bool(!x),
            (Question, Value::Bool(x)) => {
                let val = self.qubit_allocator.alloc_one();
                if x {
                    todo!();
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

    pub fn interpret(&mut self, _input: &str) -> Result<(), Vec<Box<dyn Error>>> {
        Ok(())
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
