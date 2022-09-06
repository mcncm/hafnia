//! In this module we outline the backend APIs for various target languages.
//! This is all pretty unstable for the time being, so don’t rely on it too much
//! externally.

use crate::{circuit::CircuitBuf, context::Context, util::FmtWith};

pub mod debug;
pub mod latex;
pub mod qasm;
#[cfg(feature = "summary")]
pub mod summary;

/// This type alias replaces the associated type previously attached to `Target`
pub type ObjectCode = String;

/// This is a marker trait for compile targets. Must be `Send` in order to use
/// `Box<dyn Target>` in FFI.
pub trait Target: Send {
    fn from(&self, circ: CircuitBuf, ctx: &Context) -> ObjectCode;
}

impl<T> Target for T
where
    CircuitBuf: FmtWith<T>,
    T: Send,
{
    fn from(&self, circ: CircuitBuf, _ctx: &Context) -> ObjectCode {
        format!("{}", circ.fmt_with(self))
    }
}

impl Default for Box<dyn Target> {
    fn default() -> Self {
        Box::new(null::NullTarget())
    }
}

/// A null target for testing and running partial compiler pipelines.
pub mod null {
    use super::*;

    #[derive(Debug)]
    pub struct NullTarget();

    impl Target for NullTarget {
        fn from(&self, _circ: CircuitBuf, _ctx: &Context) -> ObjectCode {
            String::new()
        }
    }
}
