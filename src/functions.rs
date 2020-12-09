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
    /// Retrieves the function's docstring, if it has one.
    fn doc(&self) -> &Option<String>;
}

/// Functions: I’ll keep this in this file for now, but note that functions are
/// not first-class in this language, at least for the time being, as this would
/// introduce a bit of extra complexity.
#[derive(Debug, Clone)]
pub struct UserFunc {
    pub params: Vec<String>,
    pub body: Box<Expr>,
    pub doc: Option<String>,
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
            Expr::Block(body, expr) => interp.eval_block(&body, &expr, Some(bindings), vec![]),
            _ => unreachable!(),
        }
    }

    fn doc(&self) -> &Option<String> {
        &self.doc
    }
}

pub mod builtins {
    use super::{ErrorBuf, Func, Interpreter, Value};
    use crate::circuit::Gate;
    use lazy_static::lazy_static;
    use std::collections::HashMap;

    /// This macro is helpful for synchronizing the names of builtin functions
    /// and the native functions they refer to.
    macro_rules! builtins_table {
        ($($doc:literal | $func:ident : $arity:expr),*) => {
            {
                let mut table = HashMap::new();
                $(
                    table.insert(
                        stringify!($func),
                        Builtin {
                            arity: $arity,
                            func: &$func,
                            doc: Some($doc.to_string()),
                        },
                    );
                )*
                table
            }
        };
    }

    lazy_static! {
        /// The table of builtin functions, the implementations of which are
        /// given below. Note that although `not` and `measure` are defined as builtin
        /// functions, they aren't bound to names here, since they are honored with the
        /// special `~` and `!` operators.
        #[rustfmt::skip]
        pub static ref BUILTINS: HashMap<&'static str, Builtin> = {
            builtins_table! [
                r"Return the argument, shifted by a phase of π."
                    | flip      : 1,

                r"Return the argument, after a bitwise Hadamard operation."
                    | split     : 1,

                r"Return the length of the argument."
                    | len       : 1,

                r"Return an array consisting of pairs of indices and elements \
                of the argument."
                    | enumerate : 1,

                r"Zip together two arrays, returning an array of pairs of \
                elements."
                    | zip       : 2,

                r"Reverse an array or tuple."
                    | reversed  : 1,

                r"Allocate memory from the QRAM."
                    | qalloc    : 2,

                r"Free memory to the QRAM."
                    | free      : 1
            ]
        };
    }

    /// Type representing a builtin function. These are best implemented with a
    /// separate data structure from user-defined functions because the `func`
    /// field is here a native function, rather than a `Block` expression.
    #[derive(Clone)]
    pub struct Builtin {
        arity: usize,
        func: &'static (dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, ErrorBuf> + Sync),
        doc: Option<String>,
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

        fn doc(&self) -> &Option<String> {
            &self.doc
        }
    }

    //////////////////////////////////////
    // Builtin function implementations //
    //////////////////////////////////////

    /// This macro builds a function that bitwise-broadcasts a single gate.
    macro_rules! gate_function {
        ($name:ident, $gate:ident, $meas:expr; $($typ:ident),+) => {
            pub fn $name(interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
                match args[0] {

                    // Q_Bool must be handled separately--at least for the time
                    // being--because its structure differs form the Q_UXX
                    // values: rather than containing a `[usize; 1]`, it contains a `usize`.
                    Value::Q_Bool(qb) => {
                        interp.compile_gate(Gate::$gate(qb));

                        // We add a special condition for the return value.
                        // Because $meas is a constant, the branch will be
                        // eliminated and impose no runtime cost.
                        if $meas {
                            // For now, the measurement operator simply returns
                            // the unit type, rather than a measured value.
                            Ok(Value::Measured(Box::new(Value::Q_Bool(qb))))
                        } else {
                            Ok(Value::Q_Bool(qb))
                        }
                    }

                    $(
                        Value::$typ(qbs) => {
                        for qb in qbs.iter() {
                            interp.compile_gate(Gate::$gate(*qb))
                        }
                        if $meas {
                            Ok(Value::Measured(Box::new(Value::$typ(qbs))))
                        } else {
                            Ok(Value::$typ(qbs))
                        }
                    }
                    ),+

                    _ => todo!(),
                }
            }
        };
    }

    gate_function![not, X, false; Q_U8, Q_U16, Q_U32];
    gate_function![flip, Z, false; Q_U8, Q_U16, Q_U32];
    gate_function![split, H, false; Q_U8, Q_U16, Q_U32];
    gate_function![measure, M, true; Q_U8, Q_U16, Q_U32];

    fn len(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
        use Value::{Array, Tuple};
        match &args[0] {
            Array(data) | Tuple(data) => Ok(Value::U32(data.len() as u32)),
            _ => panic!("Violated typing invariant!"), // error
        }
    }

    // Functions for manipulating iterators

    fn enumerate(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
        use std::convert::TryInto;
        use Value::{Array, Tuple};
        match &args[0] {
            Array(data) => {
                let pairs = data
                    .iter()
                    .enumerate()
                    // TODO Ok, I should *really* add a "usize" type that’s
                    // identical to the underlying Rust one.
                    .map(|(i, elem)| Tuple(vec![Value::U32(i.try_into().unwrap()), elem.clone()]))
                    .collect();
                Ok(Array(pairs))
            }
            _ => panic!("Violated typing invariant!"), // error
        }
    }

    fn zip(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
        use Value::{Array, Tuple};
        match (&args[0], &args[1]) {
            (Array(data_l), Array(data_r)) => {
                let pairs = data_l
                    .iter()
                    .zip(data_r.iter())
                    .map(|(item_l, item_r)| Tuple(vec![item_l.clone(), item_r.clone()]))
                    .collect();
                Ok(Array(pairs))
            }
            _ => panic!("Violated typing invariant!"), // error
        }
    }

    fn reversed(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, ErrorBuf> {
        use Value::{Array, Tuple};
        match &args[0] {
            Array(data) => {
                let data_rev = data.iter().rev().map(|item| item.clone()).collect();
                Ok(Array(data_rev))
            }
            Tuple(data) => {
                let data_rev = data.iter().rev().map(|item| item.clone()).collect();
                Ok(Tuple(data_rev))
            }
            _ => panic!("Violated typing invariant!"), // error
        }
    }

    // Dynamic allocation

    fn qalloc(interp: &mut Interpreter, _args: &[Value]) -> Result<Value, ErrorBuf> {
        match &mut interp.qram {
            Some(_) => {
                todo!();
            }
            None => {
                todo!();
            }
        }
    }

    fn free(interp: &mut Interpreter, _args: &[Value]) -> Result<Value, ErrorBuf> {
        match &mut interp.qram {
            Some(_) => {
                todo!();
            }
            None => {
                todo!();
            }
        }
    }
}
