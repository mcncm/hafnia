use crate::{ast::Expr, mir::Proj, num::USmall, token::Token};
use std::fmt;

/// The enum of all the classical Cavy values, comprising the unit type
/// booleans, integers of several sizes, and the quantized counterparts of these
/// types. The quantized integer types are all little-endian by default. In
/// future versions of the compiler, it may be possible to specify the
/// endianness of the backend.
#[derive(Debug, PartialEq, Eq, Clone)]
#[allow(non_camel_case_types)]
pub enum Value {
    // NOTE Here the unit value isn't equal to the empty tuple value, although
    // the types are equal. Is that a problem?
    Unit,

    // Base types
    Bool(bool),
    U2(USmall<2>),
    U4(USmall<4>),
    U8(u8),
    U16(u16),
    U32(u32),

    // All composite types are to be represented as lists
    List(Vec<Value>),

    // Provisional, experimental type
    Ord,
}

impl Value {
    pub fn size(&self) -> usize {
        use Value::*;
        match self {
            Unit => 0,
            Bool(_) => 1,
            U2(_) => 2,
            U4(_) => 4,
            U8(_) => 8,
            U16(_) => 16,
            U32(_) => 32,
            List(elems) => elems.iter().map(|elem| elem.size()).sum(),
            Ord => todo!(),
        }
    }

    // TODO: [PERF] the allocation here is very unsatisfying; unfortunately,
    // it's not straightforward to do this entirely with allocation-free lazy
    // iterators.
    //
    // Could *at least* use a bitvec or something
    pub fn bits(&self) -> Vec<bool> {
        match self {
            Value::Unit => vec![],
            Value::Bool(b) => vec![*b],
            // don't bother trying to make these nice and generic (yet); it
            // turns out to be a slight pain
            Value::U2(n) => (0..2).map(|i| (u8::from(*n) & (1 << i)) != 0).collect(),
            Value::U4(n) => (0..4).map(|i| (u8::from(*n) & (1 << i)) != 0).collect(),
            Value::U8(n) => (0..8).map(|i| (n & (1 << i)) != 0).collect(),
            Value::U16(n) => (0..16).map(|i| (n & (1 << i)) != 0).collect(),
            Value::U32(n) => (0..32).map(|i| (n & (1 << i)) != 0).collect(),
            Value::List(elems) => elems.iter().map(|e| e.bits()).flatten().collect(),
            Value::Ord => panic!(),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Bool(x) => *x,
            _ => todo!(),
        }
    }

    /// Get the path positions held by this value
    pub fn slot(&self, elem: usize) -> Option<&Value> {
        match self {
            Value::List(factors) => {
                if elem < factors.len() {
                    Some(&factors[elem])
                } else {
                    None
                }
            }
            // Invariant enforced by type checker
            _ => unreachable!(),
        }
    }

    /// Get a mutable reference to a slot, whether or not there was a value
    /// there before. If there was not, put a unit value into it.
    pub fn slot_mut(&mut self, elem: usize) -> &mut Value {
        if let Value::Unit = self {
            let factors = std::iter::repeat(Value::Unit).take(elem).collect();
            *self = Value::List(factors);
        }

        match self {
            Value::List(factors) => {
                if elem >= factors.len() {
                    let diff = 1 + elem - factors.len();
                    factors.extend(std::iter::repeat(Value::Unit).take(diff));
                }
                &mut factors[elem]
            }
            // Invariant enforced by type checker
            _ => {
                unreachable!()
            }
        }
    }

    /// Follow a path to its end from this value
    pub fn follow(&self, path: &[Proj]) -> Option<&Value> {
        let mut node = Some(self);
        for elem in path {
            // Derefs don't affect anything!
            if let Proj::Field(field) = elem {
                node = match node {
                    Some(node) => node.slot(*field),
                    None => return None,
                }
            }
        }
        node
    }

    // NOTE Is it a "problem" that the `follow` and `follow_mut` APIs aren't
    // symmetric?
    /// Follow a path to its end from this value, mutably:
    pub fn follow_mut(&mut self, path: &[Proj]) -> &mut Value {
        let mut node = self;
        for elem in path {
            if let Proj::Field(field) = elem {
                node = node.slot_mut(*field);
            }
        }
        node
    }
}

impl From<bool> for Value {
    fn from(val: bool) -> Value {
        Value::Bool(val)
    }
}

impl From<USmall<2>> for Value {
    fn from(val: USmall<2>) -> Value {
        Value::U2(val)
    }
}

impl From<USmall<4>> for Value {
    fn from(val: USmall<4>) -> Value {
        Value::U4(val)
    }
}

impl From<u8> for Value {
    fn from(val: u8) -> Value {
        Value::U8(val)
    }
}

impl From<u16> for Value {
    fn from(val: u16) -> Value {
        Value::U16(val)
    }
}

impl From<u32> for Value {
    fn from(val: u32) -> Value {
        Value::U32(val)
    }
}

impl From<()> for Value {
    fn from((): ()) -> Value {
        Value::List(vec![])
    }
}

impl fmt::Display for Value {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Value::*;

        match self {
            Unit =>        write!(f, "()"),

            Bool(x) =>     write!(f, "{}", x),
            U2(x) =>       write!(f, "{}", x),
            U4(x) =>       write!(f, "{}", x),
            U8(x) =>       write!(f, "{}", x),
            U16(x) =>      write!(f, "{}", x),
            U32(x) =>      write!(f, "{}", x),

            List(data) => {
                let repr = data
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "({})", repr)
            }

            Ord => f.write_str("ord"),
        }
    }
}
