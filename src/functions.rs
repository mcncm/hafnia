use crate::{
    ast::Expr,
    environment::{Key, Nameable},
    errors::ErrorBuf,
    interpreter::Interpreter,
    values::Value,
};
use std::{collections::HashMap, fmt::Debug};

/// this is like an implementable Fn. Some notes on this trait:
///
/// It’s a little bit awkward, because all of our functions will be held in
/// within an environment owned by our interpreter. However, this signature
/// requires that we pass in a mutable reference to the same interpreter. This
/// means that it must be stored within an `Rc` or other smart pointer, which
/// might have some runtime performance cost. Moreover, it might be a hint that
/// the design needs work.
pub trait Func: Debug {
    fn call(&self, interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf>;
}

/// Functions: I’ll keep this in this file for now, but note that functions are
/// not first-class in this language, at least for the time being, as this would
/// introduce a bit of extra complexity.
#[derive(Debug, Clone)]
pub struct UserFunc {
    pub params: Vec<String>,
    pub body: Box<Expr>,
}

impl Func for UserFunc {
    fn call(&self, interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
        if args.len() != self.params.len() {
            todo!(); // Should return return an error
        }

        // TODO this is really *not correct*: arguments should be
        // coevaluated. Because I don’t want to deal with that just yet, I’m
        // accepting only identifier arguments.
        //
        // Actually, on second though, should they be? Maybe there should
        // really be a distinction between passing by value and passing by
        // reference.
        //
        // FIXME unwrap for testing
        let bindings: HashMap<Key, Nameable> = self
            .params
            .iter()
            .zip(args.iter())
            .map(|(key, val)| (key.clone(), Nameable::Value(val.clone())))
            .collect();

        match &*self.body {
            Expr::Block(body, expr) => interp.eval_block(&body, &expr, Some(bindings), None),
            _ => unreachable!(),
        }
    }
}

pub mod builtins {
    use super::{ErrorBuf, Func, Interpreter, Value};
    use crate::circuit::Gate;
    use lazy_static::lazy_static;
    use std::collections::HashMap;

    lazy_static! {
        /// The table of builtin functions, the implementations of which are
        /// given below
        #[rustfmt::skip]
        pub static ref BUILTINS: HashMap<&'static str, Builtin> = {
            let mut m = HashMap::new();
            m.insert("flip", Builtin { arity: 1, func: &flip });
            m.insert("split", Builtin { arity: 1, func: &split });
            m
        };
    }

    /// Type representing a builtin function
    #[derive(Clone)]
    pub struct Builtin {
        arity: usize,
        func: &'static (dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, ErrorBuf> + Sync),
    }

    impl std::fmt::Debug for Builtin {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "<Builtin of arity {}>", self.arity)
        }
    }

    impl Func for Builtin {
        fn call(&self, interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
            if self.arity != args.len() {
                todo!();
            }
            (self.func)(interp, args)
        }
    }

    //////////////////////////////////////
    // Builtin function implementations //
    //////////////////////////////////////

    /// This macro builds a function that applies a single gate to a qubit.
    macro_rules! gate_function {
        ($name:ident, $gate:ident) => {
            fn $name(interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
                match args[0] {
                    Value::Q_Bool(u) => {
                        interp.compile_gate(Gate::$gate(u));
                        Ok(Value::Q_Bool(u))
                    }
                    _ => todo!(),
                }
            }
        };
    }

    gate_function![flip, Z];
    gate_function![split, H];
}
